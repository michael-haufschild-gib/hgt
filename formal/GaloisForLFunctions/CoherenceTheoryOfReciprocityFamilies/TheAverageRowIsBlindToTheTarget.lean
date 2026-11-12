import GaloisForLFunctions.FamilyContinuationTheory.TheLocalFactorOfThePoissonSeriesIsExplicit
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheWallOfTheFrameIsAPhaseLFunction

/-!
# The average row is blind to the target

The rows of the Poisson series of the cubic-theta probe are indexed by sixth-power-free `u`. At a
good prime `π ∤ u` the complete local series of row `u` depends on `u` only through the sextic
residue `ρ = χ_π(u) ∈ μ₆`, and sums to (`hasSum_localTerm_rowLocalSum`)

`P(ρ) = (1 − V)⁻¹ + ρY(1 − ρY)⁻¹ + (1 − R)⁻¹ (R(1 − Q⁻¹)(1 − V)⁻¹ + ρYR − η ρ⁻¹ X
        − η(Q − 1)XYV(1 − V)⁻¹)`,

`X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`, `R = κ⁶Q⁴X⁶V`. The term `−η ρ⁻¹ X` is the local factor
`1 − η(π)N(π)^{−x}` of the reciprocal `1/L(x, ηχ_u)` of the target: it sits in the mode `ρ⁻¹`.

As `u` runs over the residues prime to `π`, `ρ` is equidistributed on `μ₆`. The **average row**
(the principal component of the row family, the part that is coherent along the principal twists)
is the mean of `P` over `μ₆` (`average_rowLocalSum`):

`⟨P⟩ = (1 − V)⁻¹ + Y⁶(1 − Y⁶)⁻¹ + (1 − R)⁻¹ (R(1 − Q⁻¹) − η(Q − 1)XYV)(1 − V)⁻¹`.

The modes `ρ` and `ρ⁻¹` average to zero, and with them the target. After the factors of
`ζ(6z)`, `ζ(6w)` and `L(6x + 6z − 4, ψ₆η⁶)` are taken out, the average local factor is
`G = 1 − Y⁶V − R(Q⁻¹ + Y⁶ − Y⁶V − Y⁶Q⁻¹) − η(1 − Y⁶)(Q − 1)XYV` (`averageRowFactor_eq`), within
`9 Q^{−e}` of one whenever every monomial is (`norm_averageRowFactor_sub_one_le`). On the floor
region of the probe (`Re x ≥ 51/100`, `Re z ≥ 17/50`, `Re w ≥ −1/100`, `Re(x + w) ≥ 1`) the
exponent is at least `198/100`, so the average row is an absolutely convergent Euler product,
holomorphic and without zeros in `x` (`exists_averageRowCorrection_cutoff`): it carries no
reciprocal of the target. The principal row `ρ = 1` keeps the term `−ηX`.

So the saturation of the floor bin along the principal twists, which makes the triangle bound
`R = 1` sharp, is target-free: what the signed estimate of the floor bin has to control is the
non-principal part of the row family.
-/

noncomputable section

open Complex NumberField IsDedekindDomain Finset
open scoped Classical

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### The row local sum as a function of the residue `ρ` -/

/-- The complete local series of a row at a good prime not dividing it, as a function of the
sextic residue `ρ = χ_π(u)`. -/
def rowLocalSum (Q R ηp X Y V ρ : ℂ) : ℂ :=
  (1 - V)⁻¹ + ρ * Y * (1 - ρ * Y)⁻¹ +
    (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ + ρ * Y * R - ηp * ρ⁻¹ * X -
      ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)

/-- The average of the row local sum over the sextic residues. -/
def averageRowLocalSum (Q R ηp X Y V : ℂ) : ℂ :=
  (1 - V)⁻¹ + Y ^ 6 * (1 - Y ^ 6)⁻¹ +
    (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ - ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

include h2 hprim in
/-- **The row local series is `P(χ_π(u))`.** For `π ∤ u` and `‖V‖, ‖ρY‖, ‖R‖ < 1` the local
series of the Poisson coefficient of row `u` at `π` sums to `rowLocalSum` at `ρ = χ_π(u)`. -/
theorem hasSum_localTerm_rowLocalSum (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hV : ‖V‖ < 1)
    (hW : ‖complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y‖ < 1)
    (hR : ‖primeR π ηp X V‖ < 1) :
    HasSum (localTerm π ηp X Y V u 0)
      (rowLocalSum (primeQ π) (primeR π ηp X V) ηp X Y V
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))) := by
  have h := hasSum_localTerm π hlam h2 hprim ηp X Y V hu (j := 0) (by norm_num) hV hW hR
  convert h using 1
  simp (config := { decide := true }) only [Fin.sum_univ_two, baseSum, ↓reduceIte]
  unfold rowLocalSum
  ring

end Prime

/-! ### The average over `μ₆` -/

/-- `Σ_{i<6} ζ^i Y/(1 − ζ^i Y) = 6Y⁶/(1 − Y⁶)` for a primitive sixth root `ζ` and `‖Y‖ < 1`. -/
theorem sum_geom_primitive_six {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) {Y : ℂ} (hY : ‖Y‖ < 1) :
    ∑ i ∈ range 6, ζ ^ i * Y * (1 - ζ ^ i * Y)⁻¹ = 6 * (Y ^ 6 * (1 - Y ^ 6)⁻¹) := by
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one (by norm_num)
  -- each term is a geometric series
  have hterm : ∀ i ∈ range 6, HasSum (fun k : ℕ => (ζ ^ i * Y) ^ (k + 1))
      (ζ ^ i * Y * (1 - ζ ^ i * Y)⁻¹) := by
    intro i _
    have hr : ‖ζ ^ i * Y‖ < 1 := by rw [norm_mul, norm_pow, hζn, one_pow, one_mul]; exact hY
    have h := (hasSum_geometric_of_norm_lt_one hr).mul_left (ζ ^ i * Y)
    have hf : (fun k : ℕ => (ζ ^ i * Y) ^ (k + 1)) = fun k => ζ ^ i * Y * (ζ ^ i * Y) ^ k := by
      funext k
      rw [pow_succ']
    rw [hf]
    exact h
  have hsum := hasSum_sum hterm
  -- the inner sums over `i` vanish unless `6 ∣ k + 1`
  have hinner : ∀ k : ℕ, ∑ i ∈ range 6, (ζ ^ i * Y) ^ (k + 1) =
      if 6 ∣ k + 1 then 6 * Y ^ (k + 1) else 0 := by
    intro k
    have hre : ∑ i ∈ range 6, (ζ ^ i * Y) ^ (k + 1) =
        Y ^ (k + 1) * ∑ i ∈ range 6, (ζ ^ (k + 1)) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i (k + 1), mul_comm]
    rw [hre]
    split_ifs with hd
    · have h1 : ζ ^ (k + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).mpr hd
      simp [h1]
      ring
    · have h1 : ζ ^ (k + 1) ≠ 1 := fun h => hd ((hζ.pow_eq_one_iff_dvd _).mp h)
      have h6 : (ζ ^ (k + 1)) ^ 6 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
        one_pow]
      rw [geom_sum_eq h1, h6, sub_self, zero_div, mul_zero]
  simp_rw [hinner] at hsum
  -- reindex along `k = 6m + 5`
  have hY6 : ‖Y ^ 6‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hY (by norm_num)
  have hgeo : HasSum (fun m : ℕ => 6 * Y ^ (6 * m + 6)) (6 * (Y ^ 6 * (1 - Y ^ 6)⁻¹)) := by
    have h := ((hasSum_geometric_of_norm_lt_one hY6).mul_left (Y ^ 6)).mul_left 6
    have hf : (fun m : ℕ => 6 * Y ^ (6 * m + 6)) = fun m => 6 * (Y ^ 6 * (Y ^ 6) ^ m) := by
      funext m
      rw [show 6 * m + 6 = 6 + 6 * m by ring, pow_add, pow_mul]
    rw [hf]
    exact h
  have hinj : Function.Injective fun m : ℕ => 6 * m + 5 := fun a b h => by
    simp only at h
    omega
  have hcomp := (hinj.hasSum_iff (f := fun k : ℕ => if 6 ∣ k + 1 then 6 * Y ^ (k + 1) else 0)
    (a := 6 * (Y ^ 6 * (1 - Y ^ 6)⁻¹)) (fun k hk => by
      rw [if_neg]
      rintro ⟨m, hm⟩
      exact hk ⟨m - 1, by
        have : 1 ≤ m := by omega
        simp only
        omega⟩)).mp (by
      convert hgeo using 1
      funext m
      simp only [Function.comp, show 6 ∣ 6 * m + 5 + 1 from ⟨m + 1, by ring⟩, if_true])
  exact hsum.unique hcomp

/-- **The average row.** For a primitive sixth root of unity `ζ`, `‖Y‖ < 1`, the mean of the row
local sum over `ρ ∈ μ₆` is `averageRowLocalSum`: the modes `ρ`, `ρ⁻¹` vanish, and with them the
local factor of the reciprocal of the target. -/
theorem average_rowLocalSum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (Q R ηp X Y V : ℂ)
    (hY : ‖Y‖ < 1) :
    (1 / 6 : ℂ) * ∑ i ∈ range 6, rowLocalSum Q R ηp X Y V (ζ ^ i) =
      averageRowLocalSum Q R ηp X Y V := by
  have hs1 : ∑ i ∈ range 6, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hs2 : ∑ i ∈ range 6, (ζ ^ i)⁻¹ = 0 := by
    have := hζ.inv.geom_sum_eq_zero (by norm_num)
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => (inv_pow ζ i).symm
  have hgeo := sum_geom_primitive_six hζ hY
  have hexp : ∀ ρ : ℂ, rowLocalSum Q R ηp X Y V ρ =
      ((1 - V)⁻¹ + (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ -
        ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)) + ρ * Y * (1 - ρ * Y)⁻¹ +
        ((1 - R)⁻¹ * Y * R) * ρ - ((1 - R)⁻¹ * ηp * X) * ρ⁻¹ := by
    intro ρ
    unfold rowLocalSum
    ring
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hs1, hs2, hgeo, Finset.sum_const, Finset.card_range]
  unfold averageRowLocalSum
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero, sub_zero]
  ring

/-! ### The average local factor -/

/-- The average local factor after `ζ(6z)`, `ζ(6w)` and the phase `L`-function are taken out. -/
def averageRowFactor (Q R ηp X Y V : ℂ) : ℂ :=
  1 - Y ^ 6 * V - R * (Q⁻¹ + Y ^ 6 - Y ^ 6 * V - Y ^ 6 * Q⁻¹) -
    ηp * (1 - Y ^ 6) * (Q - 1) * X * Y * V

/-- **The average row factors through `ζ(6z) ζ(6w) L(6x + 6z − 4)`.** -/
theorem averageRowFactor_eq {Q R ηp X Y V : ℂ} (hV : 1 - V ≠ 0) (hY : 1 - Y ^ 6 ≠ 0)
    (hR : 1 - R ≠ 0) :
    averageRowLocalSum Q R ηp X Y V * ((1 - V) * (1 - Y ^ 6) * (1 - R)) =
      averageRowFactor Q R ηp X Y V := by
  unfold averageRowLocalSum averageRowFactor
  field_simp
  ring

/-- **The principal row keeps the target.** At `ρ = 1` the local sum is the average plus the modes
`ρ`, `ρ⁻¹` and `ζ(w)`: its difference from the average contains `−(1 − R)⁻¹ η X`, the local term
of `1/L(x, η)`. -/
theorem rowLocalSum_one_sub_average (Q R ηp X Y V : ℂ) :
    rowLocalSum Q R ηp X Y V 1 - averageRowLocalSum Q R ηp X Y V =
      Y * (1 - Y)⁻¹ - Y ^ 6 * (1 - Y ^ 6)⁻¹ + (1 - R)⁻¹ * (Y * R - ηp * X) := by
  unfold rowLocalSum averageRowLocalSum
  simp only [one_mul, inv_one, mul_one]
  ring

/-- **The defect of the average factor.** `G − 1` is a signed sum of nine monomials; if each is
bounded by `b` (with `‖η‖ ≤ 1`), then `‖G − 1‖ ≤ 9 b`. -/
theorem norm_averageRowFactor_sub_one_le {Q R ηp X Y V : ℂ} {b : ℝ} (hη : ‖ηp‖ ≤ 1)
    (h1 : ‖Y ^ 6 * V‖ ≤ b) (h2 : ‖R * Q⁻¹‖ ≤ b) (h3 : ‖R * Y ^ 6‖ ≤ b)
    (h4 : ‖R * Y ^ 6 * V‖ ≤ b) (h5 : ‖R * Y ^ 6 * Q⁻¹‖ ≤ b) (h6 : ‖Q * X * Y * V‖ ≤ b)
    (h7 : ‖X * Y * V‖ ≤ b) (h8 : ‖Q * X * Y ^ 7 * V‖ ≤ b) (h9 : ‖X * Y ^ 7 * V‖ ≤ b) :
    ‖averageRowFactor Q R ηp X Y V - 1‖ ≤ 9 * b := by
  have hrw : averageRowFactor Q R ηp X Y V - 1 =
      -(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V + R * Y ^ 6 * Q⁻¹ -
        ηp * (Q * X * Y * V) + ηp * (X * Y * V) + ηp * (Q * X * Y ^ 7 * V) -
          ηp * (X * Y ^ 7 * V) := by
    unfold averageRowFactor
    ring
  have hη' : ∀ z : ℂ, ‖z‖ ≤ b → ‖ηp * z‖ ≤ b := fun z hz => by
    rw [norm_mul]
    calc ‖ηp‖ * ‖z‖ ≤ 1 * b := mul_le_mul hη hz (norm_nonneg _) zero_le_one
      _ = b := one_mul b
  rw [hrw]
  have e1 := norm_sub_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V + R * Y ^ 6 * Q⁻¹ -
        ηp * (Q * X * Y * V) + ηp * (X * Y * V) + ηp * (Q * X * Y ^ 7 * V))
      (ηp * (X * Y ^ 7 * V))
  have e2 := norm_add_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V + R * Y ^ 6 * Q⁻¹ -
        ηp * (Q * X * Y * V) + ηp * (X * Y * V)) (ηp * (Q * X * Y ^ 7 * V))
  have e3 := norm_add_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V + R * Y ^ 6 * Q⁻¹ -
        ηp * (Q * X * Y * V)) (ηp * (X * Y * V))
  have e4 := norm_sub_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V + R * Y ^ 6 * Q⁻¹)
      (ηp * (Q * X * Y * V))
  have e5 := norm_add_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6 + R * Y ^ 6 * V) (R * Y ^ 6 * Q⁻¹)
  have e6 := norm_add_le (-(Y ^ 6 * V) - R * Q⁻¹ - R * Y ^ 6) (R * Y ^ 6 * V)
  have e7 := norm_sub_le (-(Y ^ 6 * V) - R * Q⁻¹) (R * Y ^ 6)
  have e8 := norm_sub_le (-(Y ^ 6 * V)) (R * Q⁻¹)
  rw [norm_neg] at e8
  linarith [hη' _ h6, hη' _ h7, hη' _ h8, hη' _ h9]

/-! ### The average row over a number field -/

/-- The average local factor at a prime of norm `Q`, with phase `κ`, character value `η` and
`X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`, `R = κ⁶Q⁴X⁶V`. -/
def averageRowLocalFactor (Q : ℝ) (κ ηp x w z : ℂ) : ℂ :=
  averageRowFactor (Q : ℂ) (κ ^ 6 * (Q : ℂ) ^ 4 * ((Q : ℂ) ^ (-x)) ^ 6 * (Q : ℂ) ^ (-(6 * z)))
    ηp ((Q : ℂ) ^ (-x)) ((Q : ℂ) ^ (-w)) ((Q : ℂ) ^ (-(6 * z)))

theorem norm_cpow_neg_eq {Q : ℝ} (hQ : 0 < Q) (x : ℂ) : ‖(Q : ℂ) ^ (-x)‖ = Q ^ (-x.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ, neg_re]

/-- **The average factor is close to one on the floor region.** For `Q ≥ 1`, `‖κ‖, ‖η‖ ≤ 1`,
`Re x ≥ 51/100`, `Re z ≥ 17/50`, `Re w ≥ −1/100`, `Re(x + w) ≥ 1`: `‖G − 1‖ ≤ 9 Q^{−198/100}`. -/
theorem norm_averageRowLocalFactor_sub_one_le {Q : ℝ} (hQ : 1 ≤ Q) {κ ηp x w z : ℂ}
    (hκ : ‖κ‖ ≤ 1) (hη : ‖ηp‖ ≤ 1) (hx : 51 / 100 ≤ x.re) (hz : 17 / 50 ≤ z.re)
    (hw : -(1 / 100) ≤ w.re) (hxw : 1 ≤ x.re + w.re) :
    ‖averageRowLocalFactor Q κ ηp x w z - 1‖ ≤ 9 * Q ^ (-(198 / 100 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hX : ‖(Q : ℂ) ^ (-x)‖ = Q ^ (-x.re) := norm_cpow_neg_eq hQ0 x
  have hY : ‖(Q : ℂ) ^ (-w)‖ = Q ^ (-w.re) := norm_cpow_neg_eq hQ0 w
  have hV : ‖(Q : ℂ) ^ (-(6 * z))‖ = Q ^ (-(6 * z.re)) := by
    rw [norm_cpow_neg_eq hQ0]
    simp
  have hQn : ‖(Q : ℂ)‖ = Q ^ (1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_one]
  have hQi : ‖(Q : ℂ)⁻¹‖ = Q ^ (-1 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_neg_one]
  have hQ4 : ‖(Q : ℂ) ^ 4‖ = Q ^ (4 : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hQ0.le, ← Real.rpow_natCast]
    norm_num
  have hpw : ∀ (a : ℝ) (n : ℕ), (Q ^ a) ^ n = Q ^ (n * a) := fun a n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, mul_comm]
  have hmul : ∀ a b : ℝ, Q ^ a * Q ^ b = Q ^ (a + b) := fun a b => (Real.rpow_add hQ0 a b).symm
  have hle : ∀ a : ℝ, a ≤ -(198 / 100) → Q ^ a ≤ Q ^ (-(198 / 100 : ℝ)) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hQ ha
  have hκ6 : ‖κ ^ 6‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hκ
  -- the norm of `R` is at most `Q^{4 − 6 Re x − 6 Re z}`
  have hR : ∀ c : ℝ, 0 ≤ c → ‖κ ^ 6 * (Q : ℂ) ^ 4 * ((Q : ℂ) ^ (-x)) ^ 6 *
      (Q : ℂ) ^ (-(6 * z))‖ * c ≤ Q ^ (4 - 6 * x.re - 6 * z.re) * c := by
    intro c hc
    refine mul_le_mul_of_nonneg_right ?_ hc
    rw [norm_mul, norm_mul, norm_mul, norm_pow (Q ^ (-x) : ℂ), hX, hV, hQ4, hpw]
    calc ‖κ ^ 6‖ * Q ^ (4 : ℝ) * Q ^ ((6 : ℕ) * -x.re) * Q ^ (-(6 * z.re))
        ≤ 1 * Q ^ (4 : ℝ) * Q ^ ((6 : ℕ) * -x.re) * Q ^ (-(6 * z.re)) := by gcongr
      _ = Q ^ (4 - 6 * x.re - 6 * z.re) := by
          rw [one_mul, hmul, hmul]
          congr 1
          push_cast
          ring
  unfold averageRowLocalFactor
  refine norm_averageRowFactor_sub_one_le hη ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [norm_mul, norm_pow, hY, hV, hpw, hmul]
    exact hle _ (by push_cast; linarith)
  · rw [norm_mul, hQi]
    exact (hR _ (Real.rpow_nonneg hQ0.le _)).trans (by rw [hmul]; exact hle _ (by linarith))
  · rw [norm_mul, norm_pow, hY, hpw]
    exact (hR _ (Real.rpow_nonneg hQ0.le _)).trans (by
      rw [hmul]; exact hle _ (by push_cast; linarith))
  · rw [norm_mul, norm_mul, norm_pow, hY, hV, hpw, mul_assoc]
    exact (hR _ (by positivity)).trans (by
      rw [hmul, hmul]; exact hle _ (by push_cast; linarith))
  · rw [norm_mul, norm_mul, norm_pow, hY, hQi, hpw, mul_assoc]
    exact (hR _ (by positivity)).trans (by
      rw [hmul, hmul]; exact hle _ (by push_cast; linarith))
  · rw [norm_mul, norm_mul, norm_mul, hQn, hX, hY, hV, hmul, hmul, hmul]
    exact hle _ (by linarith)
  · rw [norm_mul, norm_mul, hX, hY, hV, hmul, hmul]
    exact hle _ (by linarith)
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, hQn, hX, hY, hV, hpw, hmul, hmul, hmul]
    exact hle _ (by push_cast; linarith)
  · rw [norm_mul, norm_mul, norm_pow, hX, hY, hV, hpw, hmul, hmul]
    exact hle _ (by push_cast; linarith)

/-- The average factor is entire in `x`. -/
theorem differentiable_averageRowLocalFactor {Q : ℝ} (hQ : 0 < Q) (κ ηp w z : ℂ) :
    Differentiable ℂ fun x => averageRowLocalFactor Q κ ηp x w z := by
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  unfold averageRowLocalFactor averageRowFactor
  fun_prop (disch := exact Or.inl hQ')

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The average row: the Euler product of the average local factors over the primes outside `S`,
as a function of the target variable `x`. -/
def averageRowCorrection (κ η : HeightOneSpectrum (𝓞 K) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w z x : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
    averageRowLocalFactor (primeNorm v.1) (κ v.1) (η v.1) x w z

/-- **The average row has no reciprocal of the target.** There is a norm `N₀` such that, whenever
`S` contains every prime of norm `≤ N₀`, for all phases and character values in the unit disc and
every `w`, `z` with `Re w ≥ −1/100`, `Re z ≥ 17/50`, the average row is holomorphic in `x` on
`Re x > max(51/100, 1 − Re w)` and within `½` of one there: an absolutely convergent Euler product
without zeros or poles, whatever the zeros of `L(x, η)`. -/
theorem exists_averageRowCorrection_cutoff :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ κ η : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖κ v‖ ≤ 1) → (∀ v, ‖η v‖ ≤ 1) →
      ∀ w z : ℂ, -(1 / 100) ≤ w.re → 17 / 50 ≤ z.re →
        DifferentiableOn ℂ (averageRowCorrection κ η S w z)
            {x : ℂ | max (51 / 100) (1 - w.re) < x.re} ∧
          ∀ x : ℂ, max (51 / 100) (1 - w.re) < x.re →
            ‖averageRowCorrection κ η S w z x - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_cutoff_product (K := K) (e := 198 / 100) (C := 9)
    (by norm_num) (by norm_num)
  refine ⟨N₀, hN₀, fun S hS κ η hκ hη w z hw hz => ?_⟩
  have hU : IsOpen {x : ℂ | max (51 / 100) (1 - w.re) < x.re} :=
    isOpen_lt continuous_const continuous_re
  obtain ⟨h1, h2⟩ := hcut S hS _ hU (fun v x => averageRowLocalFactor (primeNorm v) (κ v) (η v) x w z)
    (fun v hv => (differentiable_averageRowLocalFactor (by linarith) _ _ _ _).differentiableOn)
    (fun v hv x hx => by
      have hx' : max (51 / 100) (1 - w.re) < x.re := hx
      exact norm_averageRowLocalFactor_sub_one_le (by linarith) (hκ v) (hη v)
        (le_of_lt ((le_max_left _ _).trans_lt hx')) hz hw
        (by linarith [(le_max_right (51 / 100 : ℝ) (1 - w.re)).trans_lt hx']))
  exact ⟨h1, fun x hx => h2 x hx⟩

end NumberField

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
