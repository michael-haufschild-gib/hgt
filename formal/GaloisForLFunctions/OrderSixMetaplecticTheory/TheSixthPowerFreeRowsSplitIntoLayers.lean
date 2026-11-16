import GaloisForLFunctions.OrderSixMetaplecticTheory.TheColumnsAreShiftedThetaProducts

/-!
# Sixth-power-free rows split into layers

The rows of the probe are the sixth-power-free `u`. Write `u = a M` with `a` squarefree and
`M = b² c³ d⁴ e⁵` (`a, …, e` squarefree, pairwise coprime). The row character
`χ_u = χ_a χ_b² χ_c³ χ_d⁴ χ_e⁵` has conductor `a · bcde`, and its Gauss sum on the conductor
(`rowConductorGauss`) peels off the squarefree layer (`rowConductorGauss_peel`):

`g(χ_{aM}) = χ_a(bcde) χ_M(a) · g_a(1) · g(χ_M)`.

By sextic reciprocity the cross factor is a column of the squarefree layer (`rowConductorGauss_layers`):

`g(χ_{aM}) = r(a, M) · g_a(b³c²d) · g(χ_M)`,

since `χ_a(bcde · M) = χ_a(b³c⁴d⁵) \overline{χ_a(e⁶)} = \overline{χ_a(b³c²d)}`. So the squarefree layer of a
sixth-power-free row sees its higher layers as the column `n = b³c²d`; the fifth-power layer is invisible
to it. With the column dictionary (`rowRoot_column_shift_actual`), every row root number of the probe is
the root number of its higher layers times a shifted theta product of the squarefree layer at the
column `b³c²d`, twisted by quadratic data.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory CoherenceTheoryOfReciprocityFamilies MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicJacobi

/-- The Gauss sum of the row character `χ_u` on the modulus `f` (its conductor):
`Σ_{x mod f} χ_u(x) ψ_f(hx)`. -/
def rowConductorGauss (u f : O) [NeZero f] (h : O) : ℂ :=
  ∑ x : O ⧸ Ideal.span {f}, sexticSymbol (qrep x) u *
    principalTraceChar f (NeZero.ne f) (Ideal.Quotient.mk _ h * x)

theorem qrep_mk_sub (f x : O) : f ∣ qrep (Ideal.Quotient.mk (Ideal.span {f}) x) - x := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]

/-- **Peeling the squarefree layer.** If `χ_{u'}` depends only on residues modulo `m` and `a, m` are coprime:
`g(χ_{a u'}; am)(h) = χ_a(m) χ_{u'}(a) · g_a(h) · g(χ_{u'}; m)(h)`. -/
theorem rowConductorGauss_peel (a m u' : O) [NeZero a] [NeZero m] (ham : IsCoprime a m)
    (hcong : ∀ x y : O, m ∣ x - y → sexticSymbol x u' = sexticSymbol y u') (h : O) :
    haveI : NeZero (a * m) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne m)⟩
    rowConductorGauss (a * u') (a * m) h =
      sexticSymbol m a * sexticSymbol a u' * sexticGaussPow 1 a h * rowConductorGauss u' m h := by
  haveI : NeZero (a * m) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne m)⟩
  set F₂ : O ⧸ Ideal.span {m} → ℂ := fun y => sexticSymbol (qrep y) u' with hF₂
  have hsplit : ∀ x : O ⧸ Ideal.span {a * m}, sexticSymbol (qrep x) (a * u') =
      sexticResidue a (reduceLeft a m x) ^ 1 * F₂ (reduceRight a m x) := by
    intro x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [reduceLeft, reduceRight, Ideal.Quotient.factor_mk, sexticResidue_mk, pow_one, hF₂]
    rw [sexticSymbol_mul_denominator,
      sexticSymbol_congr ((dvd_mul_right a m).trans (qrep_mk_sub (a * m) z)),
      hcong _ _ ((dvd_mul_left m a).trans (qrep_mk_sub (a * m) z)),
      hcong _ _ (qrep_mk_sub m z)]
  have hx : ∀ x : O ⧸ Ideal.span {a}, sexticResidue a (Ideal.Quotient.mk _ m * x) ^ 1 =
      sexticSymbol m a * sexticResidue a x ^ 1 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, sexticResidue_mk, sexticResidue_mk, sexticSymbol_mul_numerator, pow_one, pow_one]
  have hy : ∀ y : O ⧸ Ideal.span {m}, F₂ (Ideal.Quotient.mk _ a * y) = sexticSymbol a u' * F₂ y := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [hF₂]
    rw [← map_mul, hcong _ _ (qrep_mk_sub m (a * z)), hcong _ _ (qrep_mk_sub m z),
      sexticSymbol_mul_numerator]
  unfold rowConductorGauss
  simp only [hsplit]
  rw [sum_crt_mul_traceChar a m ham (fun x => sexticResidue a x ^ 1) F₂ h]
  simp only [hx, hy, mul_assoc, ← Finset.mul_sum]
  unfold sexticGaussPow
  ring

/-- `χ_x(v^k) = χ_x(v)^k` in the denominator. -/
theorem sexticSymbol_pow_denominator (x v : O) : ∀ k : ℕ, sexticSymbol x (v ^ k) = sexticSymbol x v ^ k
  | 0 => by
    rw [pow_zero, pow_zero, sexticSymbol, symbol_one, map_one, one_pow, one_mul, quadSymbol_one_denominator]
  | k + 1 => by rw [pow_succ, pow_succ, sexticSymbol_mul_denominator, sexticSymbol_pow_denominator x v k]

/-- The higher layers `M = b²c³d⁴e⁵` only see residues modulo `bcde`. -/
theorem sexticSymbol_layers_congr (b c d e : O) {x y : O} (h : b * c * d * e ∣ x - y) :
    sexticSymbol x (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5) = sexticSymbol y (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5) := by
  have hb : b ∣ x - y := (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right b c) d) e).trans h
  have hc : c ∣ x - y := (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left c b) d) e).trans h
  have hd : d ∣ x - y := (dvd_mul_of_dvd_left (dvd_mul_left d (b * c)) e).trans h
  have he : e ∣ x - y := (dvd_mul_left e (b * c * d)).trans h
  simp only [sexticSymbol_mul_denominator, sexticSymbol_pow_denominator]
  rw [sexticSymbol_congr hb, sexticSymbol_congr hc, sexticSymbol_congr hd, sexticSymbol_congr he]

/-- `χ_a(1) = 1` for primary `a` prime to `2`. -/
theorem sexticSymbol_one_numerator {a : O} (ha : lambda ^ 2 ∣ a - 1) (ha2 : IsCoprime a 2) :
    sexticSymbol 1 a = 1 := by
  rw [sexticSymbol, symbol_one_numerator a ha, map_one, one_pow, one_mul,
    quadSymbol_one_numerator (primary_ne_zero a ha) ha2]

/-- `χ_a(y⁶) = 1` for `y` prime to `a`. -/
theorem sexticSymbol_sixth_power {a y : O} (ha : lambda ^ 2 ∣ a - 1) (ha2 : IsCoprime a 2)
    (hya : IsCoprime y a) : sexticSymbol (y ^ 6) a = 1 := by
  have hpow : ∀ k : ℕ, sexticSymbol (y ^ k) a = sexticSymbol y a ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, sexticSymbol_one_numerator ha ha2]
    | succ k ih => rw [pow_succ, pow_succ, sexticSymbol_mul_numerator, ih]
  have h3 : ringComplex (symbol y a) ^ 3 = 1 := symbol_cube ha hya
  have h2 : quadSymbol y a ^ 2 = 1 := quadSymbol_sq (primary_ne_zero a ha) ha2 hya
  rw [hpow, sexticSymbol]
  calc (ringComplex (symbol y a) ^ 2 * quadSymbol y a) ^ 6
      = (ringComplex (symbol y a) ^ 3) ^ 4 * (quadSymbol y a ^ 2) ^ 3 := by ring
    _ = 1 := by rw [h3, h2, one_pow, one_pow, mul_one]

/-- **The layers of a sixth-power-free row.** For `M = b²c³d⁴e⁵` and a squarefree layer `a` (primary, prime
to `2`, to `bcde` and to `M`): `g(χ_{aM}) = r(a, M) · g_a(b³c²d) · g(χ_M)` on the conductor `a·bcde`. The
squarefree layer sits at the column `b³c²d`. -/
theorem rowConductorGauss_layers (a b c d e : O) [NeZero a] [NeZero (b * c * d * e)]
    (ha : lambda ^ 2 ∣ a - 1) (hM : lambda ^ 2 ∣ b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5 - 1)
    (ha2 : IsCoprime a 2) (hM2 : IsCoprime (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5) 2)
    (ham : IsCoprime a (b * c * d * e)) (haM : IsCoprime a (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5)) :
    haveI : NeZero (a * (b * c * d * e)) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne _)⟩
    rowConductorGauss (a * (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5)) (a * (b * c * d * e)) 1 =
      quadraticPhase a (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5) * sexticGaussPow 1 a (b ^ 3 * c ^ 2 * d) *
        rowConductorGauss (b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5) (b * c * d * e) 1 := by
  haveI : NeZero (a * (b * c * d * e)) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne _)⟩
  set m := b * c * d * e with hm
  set M := b ^ 2 * c ^ 3 * d ^ 4 * e ^ 5 with hMdef
  set n := b ^ 3 * c ^ 2 * d with hn
  have hpeel := rowConductorGauss_peel a m M ham (fun x y hxy => sexticSymbol_layers_congr b c d e hxy) 1
  have hrec := sexticSymbol_reciprocity ha hM ha2 hM2 haM
  -- the column `n` of the squarefree layer
  have hna : IsCoprime n a := by
    have hdvd : n ∣ m ^ 3 := ⟨c * d ^ 2 * e ^ 3, by rw [hn, hm]; ring⟩
    exact (ham.pow_right (n := 3)).symm.of_isCoprime_of_dvd_left hdvd
  have hcol := sexticSymbol_mul_sexticGauss a hna 1
  rw [mul_one] at hcol
  have hsix : sexticSymbol (m * M) a * sexticSymbol n a = 1 := by
    rw [← sexticSymbol_mul_numerator, show m * M * n = m ^ 6 by rw [hm, hMdef, hn]; ring]
    exact sexticSymbol_sixth_power ha ha2 ham.symm
  have hcol' : sexticSymbol n a * sexticGaussPow 1 a n = sexticGaussPow 1 a 1 := hcol
  have hR : rowConductorGauss M (b * c * d * e) 1 = rowConductorGauss M m 1 := rfl
  have hmM : sexticSymbol m a * sexticSymbol M a = sexticSymbol (m * M) a :=
    (sexticSymbol_mul_numerator _ _ _).symm
  rw [hpeel, hrec, hR]
  linear_combination
    (-(quadraticPhase a M * rowConductorGauss M m 1 * sexticSymbol m a * sexticSymbol M a)) * hcol' +
    (quadraticPhase a M * rowConductorGauss M m 1 * sexticGaussPow 1 a n) * hsix +
    (quadraticPhase a M * rowConductorGauss M m 1 * sexticGaussPow 1 a n * sexticSymbol n a) * hmM

end GaloisForLFunctions.OrderSixMetaplecticTheory
