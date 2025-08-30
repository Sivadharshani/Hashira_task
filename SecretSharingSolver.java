package hashira;

import java.io.*;
import java.math.BigInteger;
import java.nio.file.*;
import java.util.*;
import java.util.regex.*;

public class SecretSharingSolver {
    static class Rational {
        BigInteger num, den;
        Rational(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("Zero denominator");
            if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
            BigInteger g = n.gcd(d);
            if (!g.equals(BigInteger.ONE)) { n = n.divide(g); d = d.divide(g); }
            num = n; den = d;
        }
        Rational(BigInteger n) { this(n, BigInteger.ONE); }
        Rational() { this(BigInteger.ZERO, BigInteger.ONE); }
        static Rational from(BigInteger n) { return new Rational(n, BigInteger.ONE); }
        Rational add(Rational r) { return new Rational(num.multiply(r.den).add(r.num.multiply(den)), den.multiply(r.den)); }
        Rational sub(Rational r) { return new Rational(num.multiply(r.den).subtract(r.num.multiply(den)), den.multiply(r.den)); }
        Rational mul(Rational r) { return new Rational(num.multiply(r.num), den.multiply(r.den)); }
        Rational div(Rational r) { if (r.num.equals(BigInteger.ZERO)) throw new ArithmeticException("div0"); return new Rational(num.multiply(r.den), den.multiply(r.num)); }
        boolean isZero() { return num.signum() == 0; }
        boolean equalsExact(Rational r) { return num.equals(r.num) && den.equals(r.den); }
        public String toString() { return den.equals(BigInteger.ONE) ? num.toString() : num + "/" + den; }
    }
    static class Share { int index; BigInteger x, y; Share(int i, BigInteger x, BigInteger y) { this.index = i; this.x = x; this.y = y; } }
    static String readInputFile(String[] args) throws IOException {
        String path = args.length > 0 ? args[0] : "input.json";
        return new String(Files.readAllBytes(Paths.get(path)));
    }
    static int[] parseKeys(String text) {
        Matcher m = Pattern.compile("\"keys\"\\s*:\\s*\\{[^}]*\"n\"\\s*:\\s*(\\d+)\\s*,[^}]*\"k\"\\s*:\\s*(\\d+)[^}]*\\}", Pattern.DOTALL).matcher(text);
        if (m.find()) return new int[] { Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)) };
        throw new RuntimeException("Could not parse keys");
    }
    static List<Share> parseShares(String s) {
        List<Share> out = new ArrayList<>();
        Matcher mb = Pattern.compile("\"(\\d+)\"\\s*:\\s*\\{([^}]*)\\}", Pattern.DOTALL).matcher(s);
        while (mb.find()) {
            String idxStr = mb.group(1), inner = mb.group(2);
            Matcher mBase = Pattern.compile("\"base\"\\s*:\\s*\"([^\"]+)\"").matcher(inner);
            Matcher mVal  = Pattern.compile("\"value\"\\s*:\\s*\"([^\"]+)\"").matcher(inner);
            if (!mBase.find() || !mVal.find()) continue;
            int idx = Integer.parseInt(idxStr);
            int base = Integer.parseInt(mBase.group(1).trim());
            String val = mVal.group(1).trim();
            BigInteger y = parseBigIntegerInBase(val, base);
            BigInteger x = BigInteger.valueOf(idx);
            out.add(new Share(idx, x, y));
        }
        out.sort(Comparator.comparingInt(a -> a.index));
        return out;
    }
    static BigInteger parseBigIntegerInBase(String value, int base) {
        String s = value.trim();
        if ((s.startsWith("0x") || s.startsWith("0X")) && base == 16) s = s.substring(2);
        BigInteger result = BigInteger.ZERO, b = BigInteger.valueOf(base);
        for (int i = 0; i < s.length(); ++i) {
            int d = Character.digit(s.charAt(i), base);
            if (d >= 0) result = result.multiply(b).add(BigInteger.valueOf(d));
        }
        return result;
    }
    static Rational[][] buildVandermonde(BigInteger[] xs, int k) {
        Rational[][] A = new Rational[k][k];
        for (int i = 0; i < k; ++i) {
            BigInteger xp = BigInteger.ONE;
            for (int j = 0; j < k; ++j) {
                A[i][j] = Rational.from(xp);
                xp = xp.multiply(xs[i]);
            }
        }
        return A;
    }
    static Rational[] solveLinearSystem(Rational[][] A, Rational[] ys) {
        int n = A.length;
        Rational[][] M = new Rational[n][n+1];
        for (int i = 0; i < n; ++i) { for (int j = 0; j < n; ++j) M[i][j] = A[i][j]; M[i][n] = ys[i]; }
        for (int col = 0; col < n; ++col) {
            int pivot = -1;
            for (int r = col; r < n; ++r) if (!M[r][col].isZero()) { pivot = r; break; }
            if (pivot == -1) throw new RuntimeException("Singular matrix");
            if (pivot != col) { Rational[] tmp = M[col]; M[col] = M[pivot]; M[pivot] = tmp; }
            Rational piv = M[col][col];
            for (int c = col; c <= n; ++c) M[col][c] = M[col][c].div(piv);
            for (int r = col+1; r < n; ++r) {
                Rational factor = M[r][col];
                if (factor.isZero()) continue;
                for (int c = col; c <= n; ++c) M[r][c] = M[r][c].sub(M[col][c].mul(factor));
            }
        }
        Rational[] sol = new Rational[n];
        for (int i = n-1; i >= 0; --i) {
            Rational val = M[i][n];
            for (int j = i+1; j < n; ++j) val = val.sub(M[i][j].mul(sol[j]));
            sol[i] = val;
        }
        return sol;
    }
    static Rational evaluatePoly(Rational[] coeffs, BigInteger x) {
        Rational res = new Rational(), xp = Rational.from(BigInteger.ONE), rx = Rational.from(x);
        for (Rational c : coeffs) { res = res.add(c.mul(xp)); xp = xp.mul(rx); }
        return res;
    }
    static Map<String,Object> findBestPolynomial(List<Share> shares, int k) {
        int n = shares.size();
        BigInteger[] xsAll = new BigInteger[n];
        BigInteger[] ysAll = new BigInteger[n];
        for (int i = 0; i < n; ++i) { xsAll[i] = shares.get(i).x; ysAll[i] = shares.get(i).y; }
        List<Integer> bestInliers = new ArrayList<>();
        Rational[] bestCoeffs = null;
        int[] comb = new int[k];
        for (int i = 0; i < k; ++i) comb[i] = i;
        boolean done = false;
        while (!done) {
            try {
                BigInteger[] xs = new BigInteger[k];
                Rational[] ysRat = new Rational[k];
                for (int i = 0; i < k; ++i) { xs[i] = xsAll[comb[i]]; ysRat[i] = Rational.from(ysAll[comb[i]]); }
                Rational[][] A = buildVandermonde(xs, k);
                Rational[] coeffs = solveLinearSystem(A, ysRat);
                List<Integer> inliers = new ArrayList<>();
                for (int idx = 0; idx < n; ++idx) {
                    Rational ycalc = evaluatePoly(coeffs, xsAll[idx]);
                    Rational ytrue = Rational.from(ysAll[idx]);
                    if (ycalc.equalsExact(ytrue)) inliers.add(idx);
                }
                if (bestCoeffs == null || inliers.size() > bestInliers.size()) {
                    bestCoeffs = coeffs;
                    bestInliers = inliers;
                    if (bestInliers.size() == n) break;
                }
            } catch (Exception ex) {}
            int t = k - 1;
            while (t >= 0 && comb[t] == n - k + t) t--;
            if (t < 0) done = true;
            else { comb[t]++; for (int j = t+1; j < k; ++j) comb[j] = comb[j-1] + 1; }
        }
        if (bestCoeffs == null) throw new RuntimeException("No consistent polynomial found.");
        List<Integer> outliers = new ArrayList<>();
        for (int i = 0; i < n; ++i) if (!bestInliers.contains(i)) outliers.add(i);
        Map<String,Object> out = new HashMap<>();
        out.put("coeffs", bestCoeffs);
        out.put("outliers", outliers);
        return out;
    }
    static void printResult(Rational[] coeffs, List<Integer> outliers, List<Share> shares) {
        System.out.println("{");
        System.out.println("  \"secret\": \"" + coeffs[0].toString() + "\",");
        System.out.print("  \"wrong_shares\": [");
        for (int i = 0; i < outliers.size(); ++i) {
            System.out.print("\"" + shares.get(outliers.get(i)).index + "\"");
            if (i < outliers.size() - 1) System.out.print(", ");
        }
        System.out.println("]");
        System.out.println("}");
    }
    public static void main(String[] args) throws Exception {
        String input = readInputFile(args);
        int[] keys = parseKeys(input);
        int k = keys[1];
        List<Share> shares = parseShares(input);
        if (shares.isEmpty()) { System.err.println("No shares parsed."); return; }
        Map<String,Object> best = findBestPolynomial(shares, k);
        Rational[] coeffs = (Rational[]) best.get("coeffs");
        @SuppressWarnings("unchecked") List<Integer> outliers = (List<Integer>) best.get("outliers");
        printResult(coeffs, outliers, shares);
    }
}
