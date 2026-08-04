import GaloisForLFunctions.HTGeometry.TopSymbolWimanPlace
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# Positive order from the Newton weight of the top symbol

At a Wiman--Valiron point the top symbol of an algebraic differential relation is arbitrarily small
while `z f'/f` is close to the central index.  Feeding the second fact into the first turns the top
symbol into a numerical inequality between the central index and the radius.

Write the top-degree part of the relation as `∑_c A_c(z)·T^c` with `T = f'/f`; the pure term `c = 0`
carries the coefficient `A_d := A_{(d,0)}`.  The exponent `deg A_c − c` is the Newton weight of the
term.  If the weight of the pure term strictly exceeds every other top weight, then the pure term
cannot be cancelled by the others unless the central index is at least a fixed power of the radius:

`κ·r ≤ ν(r)^d`  for arbitrarily large `r`.

That is the quantitative form of positivity of the order — the initial datum a Wiman normalisation
needs, obtained here from the two selection facts alone, with no growth classification.

The mechanism is a single comparison.  The pure coefficient has the floor `κ₀ r^{deg A_d}` past the
growth radius, each remaining coefficient the ceiling `K r^{deg A_c}`, and each factor `T` costs a
power of `2ν/r`.  Multiplying by `r^d` clears all denominators, and the Newton inequality
`deg A_c + 1 ≤ deg A_d + c` makes every remaining term lose one power of `r` against the pure term.
-/

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **A dominant pure term forces the central index to grow like a power of the radius.**  For a
transcendental entire solution of an algebraic differential relation of total degree `d ≥ 1` whose
top-degree part contains the pure term `A_d·f^d` with `A_d ≠ 0`, if every other top-degree term has
strictly smaller Newton weight — `deg A_p + 1 ≤ deg A_d + p₂` — then there is a `κ > 0` with
`κ·r ≤ ν(r)^d` at arbitrarily large radii.

At a Wiman point the top symbol is at most `κ₀/2` while the pure coefficient is at least `κ₀ r^{deg
A_d}`, so the remaining top-degree terms must carry the difference; each of them is bounded by
`K·2^d·ν^d·r^{deg A_d + d - 1}`, one power of `r` short of the pure term.  Comparing the two gives
the stated inequality. -/
theorem exists_centralIndex_pow_ge_mul_radius
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ} (hd : 1 ≤ d)
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    (hmem : ((d, 0) : ℕ × ℕ) ∈ S) (hA0 : A ((d, 0) : ℕ × ℕ) ≠ 0)
    (hNewton : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≠ 0 →
      (A p).natDegree + 1 ≤ (A ((d, 0) : ℕ × ℕ)).natDegree + p.2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      κ * r ≤ ((centralIndex a r : ℕ) : ℝ) ^ d := by
  classical
  set P0 : Polynomial ℂ := A ((d, 0) : ℕ × ℕ) with hP0def
  set e0 : ℕ := P0.natDegree with he0def
  have hlc : 0 < ‖P0.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hA0)
  set κ0 : ℝ := ‖P0.leadingCoeff‖ / 2 with hκ0def
  have hκ0 : 0 < κ0 := by rw [hκ0def]; linarith
  set K : ℝ := 1 + ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ with hKdef
  have hKsum : (0 : ℝ) ≤ ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKp : ∀ p ∈ S, (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ K := by
    intro p hp
    have hsingle := Finset.single_le_sum
      (f := fun q : ℕ × ℕ => ∑ i ∈ Finset.range ((A q).natDegree + 1), ‖(A q).coeff i‖)
      (fun q _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hp
    rw [hKdef]
    linarith
  set C : ℝ := (S.card : ℝ) * K * 2 ^ d + 1 with hCdef
  have hCpos : 0 < C := by
    have hnn : (0 : ℝ) ≤ (S.card : ℝ) * K * 2 ^ d := by positivity
    rw [hCdef]
    linarith
  refine ⟨κ0 / (2 * C), by positivity, ?_⟩
  intro R
  -- the radius past which the central index is at least one
  obtain ⟨Rν, hRν⟩ := tendsto_atTop_atTop.mp (tendsto_centralIndex_atTop ha htrans) 1
  set Rb : ℝ := max (max R 0) (max (Real.log (growthRadius P0)) (Real.log (max Rν 1))) with hRbdef
  obtain ⟨y, hy, z, hz, htop, hdefect⟩ :=
    exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel
      (η := κ0 / 2) (ε := 1) (by positivity) one_pos Rb
  set r : ℝ := Real.exp y with hrdef
  have hy0 : (0 : ℝ) ≤ y :=
    le_trans (le_trans (le_max_right R 0) (le_max_left _ _)) hy
  have hr1 : (1 : ℝ) ≤ r := Real.one_le_exp hy0
  have hrpos : (0 : ℝ) < r := by linarith
  refine ⟨r, ?_, ?_⟩
  · have h1 : R ≤ y := le_trans (le_trans (le_max_left R 0) (le_max_left _ _)) hy
    have h2 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    rw [hrdef]
    linarith
  -- the two thresholds, transported through the exponential
  have hgrow : growthRadius P0 ≤ r := by
    have h1 : Real.log (growthRadius P0) ≤ y :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
    have hpos : (0 : ℝ) < growthRadius P0 :=
      lt_of_lt_of_le zero_lt_one (one_le_growthRadius P0)
    calc growthRadius P0 = Real.exp (Real.log (growthRadius P0)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr h1
  have hνthresh : max Rν 1 ≤ r := by
    have h1 : Real.log (max Rν 1) ≤ y :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    have hpos : (0 : ℝ) < max Rν 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    calc max Rν 1 = Real.exp (Real.log (max Rν 1)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr h1
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  have hν1 : (1 : ℝ) ≤ ν := by
    have h1 : 1 ≤ centralIndex a r := hRν r (le_trans (le_max_left Rν 1) hνthresh)
    rw [hνdef]
    exact_mod_cast h1
  have hνpos : (0 : ℝ) < ν := by linarith
  have hzr : ‖z‖ = r := hz
  -- the logarithmic derivative is at most `2ν/r`
  set T : ℂ := deriv (coeffFun a) z / coeffFun a z with hTdef
  have hrT : r * ‖T‖ ≤ 2 * ν := by
    have hmd : z * deriv (coeffFun a) z / coeffFun a z = z * T := by
      rw [hTdef, mul_div_assoc]
    rw [hmd] at hdefect
    have hsplit : ‖z * T‖
        ≤ ‖z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
          + ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ := by
      simpa using norm_add_le (z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ))
        (((centralIndex a (Real.exp y) : ℕ) : ℂ))
    have hcast : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ = ν := by
      rw [hνdef, hrdef, Complex.norm_natCast]
    have hzT : ‖z * T‖ = r * ‖T‖ := by rw [norm_mul, hzr]
    rw [hzT, hcast] at hsplit
    have hone : (1 : ℝ) * ((centralIndex a (Real.exp y) : ℕ) : ℝ) = ν := by
      rw [hνdef, hrdef, one_mul]
    rw [hone] at hdefect
    linarith
  -- the pure coefficient has a floor
  have hfloor : κ0 * r ^ e0 ≤ ‖P0.eval z‖ := by
    obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hA0 (by rw [hzr]; exact hgrow)
    have hge := norm_eval_ge_of_large hA0 hz1 hz2
    rw [hzr] at hge
    exact hge
  -- each remaining top-degree coefficient has a ceiling
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  have hmemStop : ((d, 0) : ℕ × ℕ) ∈ Stop := by
    rw [hStopdef, Finset.mem_filter]
    exact ⟨hmem, by simp⟩
  have hterm : ∀ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
      ‖(A p).eval z‖ * ‖T‖ ^ p.2 * r ^ d ≤ K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0) := by
    intro p hp
    have hpne : p ≠ ((d, 0) : ℕ × ℕ) := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun q : ℕ × ℕ => q.1 + q.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hp2 : p.2 ≠ 0 := by
      intro h0
      refine hpne ?_
      have h1 : p.1 = d := by omega
      exact Prod.ext h1 h0
    have hp2d : p.2 ≤ d := by omega
    have hp21 : 1 ≤ p.2 := by omega
    have hnewt : (A p).natDegree + 1 ≤ e0 + p.2 := by
      rw [he0def, hP0def]
      exact hNewton p hpS hpd hp2
    have hAp : ‖(A p).eval z‖ ≤ K * r ^ (A p).natDegree := by
      have h1 := norm_eval_le_of_one_le (p := A p) (z := z) (by rw [hzr]; exact hr1)
      rw [hzr] at h1
      have h2 : (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ K := hKp p hpS
      have h3 : (0 : ℝ) ≤ r ^ (A p).natDegree := by positivity
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h3)
    have hexp : (A p).natDegree + (d - p.2) ≤ d - 1 + e0 := by omega
    calc ‖(A p).eval z‖ * ‖T‖ ^ p.2 * r ^ d
        = ‖(A p).eval z‖ * (r ^ p.2 * ‖T‖ ^ p.2) * r ^ (d - p.2) := by
          rw [show r ^ d = r ^ p.2 * r ^ (d - p.2) from by rw [← pow_add]; congr 1; omega]
          ring
      _ ≤ (K * r ^ (A p).natDegree) * (2 * ν) ^ p.2 * r ^ (d - p.2) := by
          have hpow : r ^ p.2 * ‖T‖ ^ p.2 ≤ (2 * ν) ^ p.2 := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hrT p.2
          gcongr
      _ = K * (2 ^ p.2 * ν ^ p.2) * r ^ ((A p).natDegree + (d - p.2)) := by
          rw [mul_pow, pow_add]
          ring
      _ ≤ K * (2 ^ d * ν ^ d) * r ^ (d - 1 + e0) := by
          gcongr
          norm_num
      _ = K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0) := by ring
  -- the master comparison
  have hsplit : ‖P0.eval z‖
      ≤ κ0 / 2 + ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
    have hsum : (A ((d, 0) : ℕ × ℕ)).eval z * T ^ (0 : ℕ)
        + ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), (A p).eval z * T ^ p.2
        = ∑ p ∈ Stop, (A p).eval z * T ^ p.2 :=
      Finset.add_sum_erase _ (fun p => (A p).eval z * T ^ p.2) hmemStop
    have heq : P0.eval z
        = (∑ p ∈ Stop, (A p).eval z * T ^ p.2)
          - ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), (A p).eval z * T ^ p.2 := by
      rw [← hsum, hP0def]
      simp
    have hbig : ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖ ≤ κ0 / 2 := by
      rw [hStopdef, hTdef]
      exact htop
    calc ‖P0.eval z‖
        ≤ ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖
          + ‖∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), (A p).eval z * T ^ p.2‖ := by
          rw [heq]
          exact norm_sub_le _ _
      _ ≤ κ0 / 2 + ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
          gcongr
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, norm_pow]
  have hcardle : ((Stop.erase ((d, 0) : ℕ × ℕ)).card : ℝ) ≤ (S.card : ℝ) := by
    have h1 : (Stop.erase ((d, 0) : ℕ × ℕ)).card ≤ S.card := by
      refine Finset.card_le_card ?_
      intro x hx
      have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
      rw [hStopdef] at hx1
      exact (Finset.mem_filter.mp hx1).1
    exact_mod_cast h1
  have hsumbound : (∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), ‖(A p).eval z‖ * ‖T‖ ^ p.2) * r ^ d
      ≤ (S.card : ℝ) * (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) := by
    rw [Finset.sum_mul]
    have hle : ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), ‖(A p).eval z‖ * ‖T‖ ^ p.2 * r ^ d
        ≤ ((Stop.erase ((d, 0) : ℕ × ℕ)).card : ℝ) * (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) := by
      have hcard := Finset.sum_le_card_nsmul (Stop.erase ((d, 0) : ℕ × ℕ))
        (fun p => ‖(A p).eval z‖ * ‖T‖ ^ p.2 * r ^ d)
        (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) hterm
      rw [nsmul_eq_mul] at hcard
      exact hcard
    have hnn : (0 : ℝ) ≤ K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0) := by positivity
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle hnn)
  -- comparing the two sides
  have hmain : κ0 * r ^ e0 * r ^ d
      ≤ (κ0 / 2) * r ^ d + (S.card : ℝ) * (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) := by
    have hrd : (0 : ℝ) ≤ r ^ d := by positivity
    have h1 : ‖P0.eval z‖ * r ^ d
        ≤ (κ0 / 2 + ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ), ‖(A p).eval z‖ * ‖T‖ ^ p.2) * r ^ d :=
      mul_le_mul_of_nonneg_right hsplit hrd
    have h2 : κ0 * r ^ e0 * r ^ d ≤ ‖P0.eval z‖ * r ^ d :=
      mul_le_mul_of_nonneg_right hfloor hrd
    rw [add_mul] at h1
    linarith
  -- clearing the common power
  have hfactor : r ^ e0 * r ^ d = r * r ^ (d - 1 + e0) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  have hdrop : r ^ d ≤ r ^ e0 * r ^ d :=
    le_mul_of_one_le_left (pow_nonneg hrpos.le d) (one_le_pow₀ hr1)
  have hpowpos : (0 : ℝ) < r ^ (d - 1 + e0) := by positivity
  have hmain' : κ0 * (r * r ^ (d - 1 + e0))
      ≤ (κ0 / 2) * (r * r ^ (d - 1 + e0))
        + (S.card : ℝ) * (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) := by
    have e1 : κ0 * r ^ e0 * r ^ d = κ0 * (r * r ^ (d - 1 + e0)) := by rw [← hfactor]; ring
    have e2 : (κ0 / 2) * r ^ d ≤ (κ0 / 2) * (r * r ^ (d - 1 + e0)) := by
      rw [← hfactor]
      exact mul_le_mul_of_nonneg_left hdrop (by linarith)
    rw [e1] at hmain
    linarith
  have hstep : (κ0 / 2) * r ≤ (S.card : ℝ) * K * 2 ^ d * ν ^ d := by
    refine le_of_mul_le_mul_right ?_ hpowpos
    calc (κ0 / 2) * r * r ^ (d - 1 + e0) = (κ0 / 2) * (r * r ^ (d - 1 + e0)) := by ring
      _ ≤ (S.card : ℝ) * (K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0)) := by linarith
      _ = (S.card : ℝ) * K * 2 ^ d * ν ^ d * r ^ (d - 1 + e0) := by ring
  have hνd : (0 : ℝ) ≤ ν ^ d := by positivity
  have hCν : (S.card : ℝ) * K * 2 ^ d * ν ^ d ≤ C * ν ^ d := by
    have hle : (S.card : ℝ) * K * 2 ^ d ≤ C := by rw [hCdef]; linarith
    exact mul_le_mul_of_nonneg_right hle hνd
  have hfinal : (κ0 / 2) * r ≤ C * ν ^ d := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
  calc κ0 * r = 2 * ((κ0 / 2) * r) := by ring
    _ ≤ 2 * (C * ν ^ d) := by linarith
    _ = ν ^ d * (2 * C) := by ring

/-! ## The complementary dominant term -/

/-- **A dominant term of maximal derivative degree caps the central index.**  If the top-degree part
has a monomial `q` carrying at least one derivative factor, carrying at least as many derivative
factors as every other top monomial, and of strictly maximal Newton weight, then that monomial cannot
be cancelled: at arbitrarily large radii

`ν(r)^{q₂}·r^{deg A_q + 1} ≤ C·r^{q₂ + 1}`.

The mechanism is the mirror image of the pure case.  Here the two-sided Wiman estimate is used from
below — `ν ≤ 2r‖f'/f‖` — so the dominant monomial has a floor, while every other top monomial loses
one power of `r` against it and, having no more derivative factors, cannot recover it from the
central index. -/
theorem centralIndex_pow_mul_pow_le_of_dominant_derivative_term
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hmaxT : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ q.2)
    (hNewton : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (q.2 - p.2) + 1 ≤ (A q).natDegree) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      ((centralIndex a r : ℕ) : ℝ) ^ q.2 * r ^ ((A q).natDegree + 1)
        ≤ Cb * r ^ (q.2 + 1) := by
  classical
  set P : Polynomial ℂ := A q with hPdef
  set e : ℕ := P.natDegree with hedef
  have hlc : 0 < ‖P.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAq)
  set κ : ℝ := ‖P.leadingCoeff‖ / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  set K : ℝ := 1 + ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ with hKdef
  have hKsum : (0 : ℝ) ≤ ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKp : ∀ p ∈ S, (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ K := by
    intro p hp
    have hsingle := Finset.single_le_sum
      (f := fun t : ℕ × ℕ => ∑ i ∈ Finset.range ((A t).natDegree + 1), ‖(A t).coeff i‖)
      (fun t _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hp
    rw [hKdef]
    linarith
  refine ⟨2 ^ (d + 1) / κ, by positivity, ?_⟩
  intro R
  obtain ⟨Rν, hRν⟩ := tendsto_atTop_atTop.mp (tendsto_centralIndex_atTop ha htrans) 1
  set Rthr : ℝ :=
    max (max (growthRadius P) (max Rν 1)) (max (2 * (S.card : ℝ) * K * 2 ^ (2 * d) / κ) 1)
    with hRthrdef
  have hRthr1 : (1 : ℝ) ≤ Rthr :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hRthrpos : (0 : ℝ) < Rthr := by linarith
  obtain ⟨y, hy, z, hz, htop, hdefect⟩ :=
    exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel
      (η := 1) (ε := 1 / 2) one_pos (by norm_num) (max (max R 0) (Real.log Rthr))
  set r : ℝ := Real.exp y with hrdef
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_trans (le_max_right R 0) (le_max_left _ _)) hy
  have hr1 : (1 : ℝ) ≤ r := Real.one_le_exp hy0
  have hrpos : (0 : ℝ) < r := by linarith
  refine ⟨r, ?_, ?_⟩
  · have h1 : R ≤ y := le_trans (le_trans (le_max_left R 0) (le_max_left _ _)) hy
    have h2 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    rw [hrdef]
    linarith
  have hthr : Rthr ≤ r := by
    have h1 : Real.log Rthr ≤ y := le_trans (le_max_right _ _) hy
    calc Rthr = Real.exp (Real.log Rthr) := (Real.exp_log hRthrpos).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr h1
  have hgrow : growthRadius P ≤ r :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hthr
  have hνthresh : max Rν 1 ≤ r :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hthr
  have hconst : 2 * (S.card : ℝ) * K * 2 ^ (2 * d) / κ ≤ r :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hthr
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  have hν1 : (1 : ℝ) ≤ ν := by
    have h1 : 1 ≤ centralIndex a r := hRν r (le_trans (le_max_left Rν 1) hνthresh)
    rw [hνdef]
    exact_mod_cast h1
  have hzr : ‖z‖ = r := hz
  set T : ℂ := deriv (coeffFun a) z / coeffFun a z with hTdef
  -- the two-sided Wiman estimate
  have hTbounds : ν ≤ 2 * (r * ‖T‖) ∧ r * ‖T‖ ≤ 2 * ν := by
    have hmd : z * deriv (coeffFun a) z / coeffFun a z = z * T := by
      rw [hTdef, mul_div_assoc]
    rw [hmd] at hdefect
    have hcast : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ = ν := by
      rw [hνdef, hrdef, Complex.norm_natCast]
    have hzT : ‖z * T‖ = r * ‖T‖ := by rw [norm_mul, hzr]
    have hup : ‖z * T‖
        ≤ ‖z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
          + ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ := by
      simpa using norm_add_le (z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ))
        (((centralIndex a (Real.exp y) : ℕ) : ℂ))
    have hlow : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
        ≤ ‖((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T‖ + ‖z * T‖ := by
      simpa using norm_add_le (((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T) (z * T)
    have hrev : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T‖
        = ‖z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ := norm_sub_rev _ _
    rw [hrev, hcast, hzT] at hlow
    rw [hzT, hcast] at hup
    have hhalf : (1 : ℝ) / 2 * ((centralIndex a (Real.exp y) : ℕ) : ℝ) = ν / 2 := by
      rw [hνdef, hrdef]
      ring
    rw [hhalf] at hdefect
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hTlow, hTup⟩ := hTbounds
  -- the dominant coefficient has a floor
  have hfloor : κ * r ^ e ≤ ‖P.eval z‖ := by
    obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hAq (by rw [hzr]; exact hgrow)
    have hge := norm_eval_ge_of_large hAq hz1 hz2
    rw [hzr] at hge
    exact hge
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  have hmemStop : q ∈ Stop := by
    rw [hStopdef, Finset.mem_filter]
    exact ⟨hq, hqd⟩
  -- every other top monomial loses a power of the radius
  have hterm : ∀ p ∈ Stop.erase q,
      ‖(A p).eval z‖ * ‖T‖ ^ p.2 * ((2 * r) ^ q.2 * r)
        ≤ K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e := by
    intro p hp
    have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hp2q : p.2 ≤ q.2 := hmaxT p hpS hpd
    have hp2d : p.2 ≤ d := by omega
    have hq2d : q.2 ≤ d := by omega
    have hnewt : (A p).natDegree + (q.2 - p.2) + 1 ≤ e := by
      rw [hedef, hPdef]
      exact hNewton p hpS hpd hpne
    have hAp : ‖(A p).eval z‖ ≤ K * r ^ (A p).natDegree := by
      have h1 := norm_eval_le_of_one_le (p := A p) (z := z) (by rw [hzr]; exact hr1)
      rw [hzr] at h1
      have h2 : (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ K := hKp p hpS
      have h3 : (0 : ℝ) ≤ r ^ (A p).natDegree := by positivity
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h3)
    have hsplitq : (2 * r) ^ q.2 * r = 2 ^ q.2 * (r ^ p.2 * (r ^ (q.2 - p.2) * r)) := by
      rw [mul_pow, show r ^ q.2 = r ^ p.2 * r ^ (q.2 - p.2) from by
        rw [← pow_add]; congr 1; omega]
      ring
    calc ‖(A p).eval z‖ * ‖T‖ ^ p.2 * ((2 * r) ^ q.2 * r)
        = ‖(A p).eval z‖ * (r ^ p.2 * ‖T‖ ^ p.2) * (2 ^ q.2 * (r ^ (q.2 - p.2) * r)) := by
          rw [hsplitq]; ring
      _ ≤ (K * r ^ (A p).natDegree) * (2 * ν) ^ p.2 * (2 ^ q.2 * (r ^ (q.2 - p.2) * r)) := by
          have hpow : r ^ p.2 * ‖T‖ ^ p.2 ≤ (2 * ν) ^ p.2 := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hTup p.2
          gcongr
      _ = K * (2 ^ (p.2 + q.2)) * ν ^ p.2 * r ^ ((A p).natDegree + (q.2 - p.2) + 1) := by
          rw [mul_pow, pow_add, pow_add, pow_add]
          ring
      _ ≤ K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e := by
          gcongr
          · norm_num
          · omega
  -- the dominant monomial cannot be cancelled
  have hsplit : ‖P.eval z‖ * ‖T‖ ^ q.2
      ≤ 1 + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
    have hsum : (A q).eval z * T ^ q.2
        + ∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2
        = ∑ p ∈ Stop, (A p).eval z * T ^ p.2 :=
      Finset.add_sum_erase _ (fun p => (A p).eval z * T ^ p.2) hmemStop
    have heq : P.eval z * T ^ q.2
        = (∑ p ∈ Stop, (A p).eval z * T ^ p.2)
          - ∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2 := by
      rw [← hsum, hPdef]
      ring
    have hbig : ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖ ≤ 1 := by
      rw [hStopdef, hTdef]
      exact htop
    have hnorm : ‖P.eval z * T ^ q.2‖ = ‖P.eval z‖ * ‖T‖ ^ q.2 := by
      rw [norm_mul, norm_pow]
    calc ‖P.eval z‖ * ‖T‖ ^ q.2
        = ‖P.eval z * T ^ q.2‖ := hnorm.symm
      _ ≤ ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖
          + ‖∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2‖ := by
          rw [heq]
          exact norm_sub_le _ _
      _ ≤ 1 + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
          gcongr
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, norm_pow]
  have hcardle : ((Stop.erase q).card : ℝ) ≤ (S.card : ℝ) := by
    have h1 : (Stop.erase q).card ≤ S.card := by
      refine Finset.card_le_card ?_
      intro x hx
      have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
      rw [hStopdef] at hx1
      exact (Finset.mem_filter.mp hx1).1
    exact_mod_cast h1
  have hmulpos : (0 : ℝ) < (2 * r) ^ q.2 * r := by positivity
  have hsumbound : (∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2) * ((2 * r) ^ q.2 * r)
      ≤ (S.card : ℝ) * (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e) := by
    rw [Finset.sum_mul]
    have hle : ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 * ((2 * r) ^ q.2 * r)
        ≤ ((Stop.erase q).card : ℝ) * (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e) := by
      have hcard := Finset.sum_le_card_nsmul (Stop.erase q)
        (fun p => ‖(A p).eval z‖ * ‖T‖ ^ p.2 * ((2 * r) ^ q.2 * r))
        (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e) hterm
      rw [nsmul_eq_mul] at hcard
      exact hcard
    have hnn : (0 : ℝ) ≤ K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e := by positivity
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle hnn)
  -- the floor of the dominant monomial, in cleared form
  have hdom : κ * r ^ e * ν ^ q.2 * r ≤ ‖P.eval z‖ * ‖T‖ ^ q.2 * ((2 * r) ^ q.2 * r) := by
    have h1 : ν ^ q.2 ≤ (2 * (r * ‖T‖)) ^ q.2 :=
      pow_le_pow_left₀ (by linarith) hTlow q.2
    have hstep : κ * r ^ e * ν ^ q.2 ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 := by
      calc κ * r ^ e * ν ^ q.2 ≤ ‖P.eval z‖ * ν ^ q.2 :=
            mul_le_mul_of_nonneg_right hfloor (by positivity)
        _ ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have hrewrite : ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 * r
        = ‖P.eval z‖ * ‖T‖ ^ q.2 * ((2 * r) ^ q.2 * r) := by
      rw [mul_pow, mul_pow, mul_pow]
      ring
    calc κ * r ^ e * ν ^ q.2 * r ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 * r :=
          mul_le_mul_of_nonneg_right hstep hrpos.le
      _ = ‖P.eval z‖ * ‖T‖ ^ q.2 * ((2 * r) ^ q.2 * r) := hrewrite
  -- assembling
  have hmain : κ * r ^ e * ν ^ q.2 * r
      ≤ 2 ^ q.2 * r ^ (q.2 + 1)
        + (S.card : ℝ) * (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e) := by
    have h1 : ‖P.eval z‖ * ‖T‖ ^ q.2 * ((2 * r) ^ q.2 * r)
        ≤ (1 + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2) * ((2 * r) ^ q.2 * r) :=
      mul_le_mul_of_nonneg_right hsplit hmulpos.le
    have h5 : (1 : ℝ) * ((2 * r) ^ q.2 * r) = 2 ^ q.2 * r ^ (q.2 + 1) := by
      rw [mul_pow, pow_add]
      ring
    rw [add_mul, h5] at h1
    linarith [hsumbound, hdom]
  -- the constant threshold removes the second term
  have habsorb : (S.card : ℝ) * (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e)
      ≤ κ / 2 * (r ^ e * ν ^ q.2 * r) := by
    have hcst : 2 * (S.card : ℝ) * K * 2 ^ (2 * d) ≤ κ * r := by
      rw [div_le_iff₀ hκ] at hconst
      linarith
    have hnn : (0 : ℝ) ≤ r ^ e * ν ^ q.2 := by positivity
    have hstep : (2 * (S.card : ℝ) * K * 2 ^ (2 * d)) * (r ^ e * ν ^ q.2)
        ≤ (κ * r) * (r ^ e * ν ^ q.2) := mul_le_mul_of_nonneg_right hcst hnn
    nlinarith [hstep]
  have h2q : (2 : ℝ) ^ q.2 ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hrq : (0 : ℝ) ≤ r ^ (q.2 + 1) := by positivity
  have hmul : 2 ^ q.2 * r ^ (q.2 + 1) ≤ 2 ^ d * r ^ (q.2 + 1) :=
    mul_le_mul_of_nonneg_right h2q hrq
  have hmainZ : κ * (r ^ e * ν ^ q.2 * r)
      ≤ 2 ^ q.2 * r ^ (q.2 + 1)
        + (S.card : ℝ) * (K * 2 ^ (2 * d) * ν ^ q.2 * r ^ e) := by
    have hz : κ * (r ^ e * ν ^ q.2 * r) = κ * r ^ e * ν ^ q.2 * r := by ring
    rw [hz]
    exact hmain
  have hfinal : κ / 2 * (r ^ e * ν ^ q.2 * r) ≤ 2 ^ d * r ^ (q.2 + 1) := by
    linarith
  have hrw : r ^ e * ν ^ q.2 * r = ν ^ q.2 * r ^ (e + 1) := by
    rw [pow_add]
    ring
  rw [hrw] at hfinal
  have hpow : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ, hpow]
  linarith

/-- **No transcendental entire solution when the dominant derivative monomial also has the larger
coefficient degree.**  Under the hypotheses of the cap, if the dominant monomial's coefficient degree
is at least its number of derivative factors, the cap bounds the central index, contradicting its
divergence. -/
theorem not_transcendental_of_dominant_derivative_term
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0) (hq1 : 1 ≤ q.2)
    (hmaxT : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ q.2)
    (hNewton : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (q.2 - p.2) + 1 ≤ (A q).natDegree)
    (hdegq : q.2 ≤ (A q).natDegree) : False := by
  classical
  obtain ⟨Cb, hCb, hbound⟩ :=
    centralIndex_pow_mul_pow_le_of_dominant_derivative_term ha hn₀ htrans hdeg hrel hq hqd hAq
      hmaxT hNewton
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Cb ≤ (M : ℝ) := ⟨⌈Cb⌉₊, Nat.le_ceil _⟩
  obtain ⟨R₀, hR₀⟩ := tendsto_atTop_atTop.mp (tendsto_centralIndex_atTop ha htrans) (M + 1)
  obtain ⟨r, hr, hcap⟩ := hbound (max R₀ 1)
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right R₀ 1) hr
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  have hνbig : ((M : ℝ) + 1) ≤ ν := by
    have h1 : M + 1 ≤ centralIndex a r := hR₀ r (le_trans (le_max_left R₀ 1) hr)
    rw [hνdef]
    exact_mod_cast h1
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hν1 : (1 : ℝ) ≤ ν := by linarith
  have hpowle : r ^ (q.2 + 1) ≤ r ^ ((A q).natDegree + 1) :=
    pow_le_pow_right₀ hr1 (by omega)
  have hpowpos : (0 : ℝ) < r ^ ((A q).natDegree + 1) := by positivity
  have hstep : ν ^ q.2 * r ^ ((A q).natDegree + 1) ≤ Cb * r ^ ((A q).natDegree + 1) :=
    le_trans hcap (mul_le_mul_of_nonneg_left hpowle hCb.le)
  have hνcap : ν ^ q.2 ≤ Cb := le_of_mul_le_mul_right (by linarith) hpowpos
  have hνone : ν ≤ ν ^ q.2 := by
    calc ν = ν ^ 1 := (pow_one ν).symm
      _ ≤ ν ^ q.2 := pow_le_pow_right₀ hν1 hq1
  linarith

/-! ## The face inequality

Both faces above are readings of one inequality, which holds for *every* top-degree monomial with
nonzero coefficient and carries no Newton hypothesis at all.  Normalising the relation at a Wiman
point by `(2r)^d` — enough powers of the radius to clear every derivative factor — gives a floor for
the chosen monomial and a ceiling for each of the others, in terms of the two quantities `r` and
`ν(r)` alone.  Every Newton-face conclusion is arithmetic downstream of it. -/

/-- **The Wiman face inequality.**  For a transcendental entire solution of an algebraic differential
relation of total degree at most `d`, every top-degree monomial `q` with `A_q ≠ 0` satisfies, at
arbitrarily large radii,

`‖lead A_q‖/2 · r^{deg A_q + (d − q₂)}·ν^{q₂} ≤ η·2^d·r^d + K·∑_{p ≠ q} ν^{p₂}·r^{deg A_p + (d − p₂)}`,

the sum running over the remaining top-degree monomials.  The constant `K` depends only on the
coefficients and `d`, and `η` is free. -/
theorem exists_radius_wimanFace
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
      1 ≤ ((centralIndex a r : ℕ) : ℝ) ∧
      ‖(A q).leadingCoeff‖ / 2
          * (r ^ ((A q).natDegree + (d - q.2)) * ((centralIndex a r : ℕ) : ℝ) ^ q.2)
        ≤ η * 2 ^ d * r ^ d
          + K * ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q,
              ((centralIndex a r : ℕ) : ℝ) ^ p.2 * r ^ ((A p).natDegree + (d - p.2)) := by
  classical
  set P : Polynomial ℂ := A q with hPdef
  set e : ℕ := P.natDegree with hedef
  have hlc : 0 < ‖P.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAq)
  set κ : ℝ := ‖P.leadingCoeff‖ / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  set Kc : ℝ := 1 + ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ with hKcdef
  have hKcsum : (0 : ℝ) ≤ ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hKc1 : (1 : ℝ) ≤ Kc := by rw [hKcdef]; linarith
  have hKcp : ∀ p ∈ S, (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ Kc := by
    intro p hp
    have hsingle := Finset.single_le_sum
      (f := fun t : ℕ × ℕ => ∑ i ∈ Finset.range ((A t).natDegree + 1), ‖(A t).coeff i‖)
      (fun t _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hp
    rw [hKcdef]
    linarith
  refine ⟨Kc * 2 ^ (2 * d), by positivity, ?_⟩
  intro R
  obtain ⟨Rν, hRν⟩ := tendsto_atTop_atTop.mp (tendsto_centralIndex_atTop ha htrans) 1
  set Rthr : ℝ := max (growthRadius P) (max Rν 1) with hRthrdef
  have hRthr1 : (1 : ℝ) ≤ Rthr := le_trans (le_max_right Rν 1) (le_max_right _ _)
  have hRthrpos : (0 : ℝ) < Rthr := by linarith
  obtain ⟨y, hy, z, hz, htop, hdefect⟩ :=
    exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel
      (η := η) (ε := 1 / 2) hη (by norm_num) (max (max R 0) (Real.log Rthr))
  set r : ℝ := Real.exp y with hrdef
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_trans (le_max_right R 0) (le_max_left _ _)) hy
  have hr1 : (1 : ℝ) ≤ r := Real.one_le_exp hy0
  have hrpos : (0 : ℝ) < r := by linarith
  have hthr : Rthr ≤ r := by
    have h1 : Real.log Rthr ≤ y := le_trans (le_max_right _ _) hy
    calc Rthr = Real.exp (Real.log Rthr) := (Real.exp_log hRthrpos).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr h1
  have hgrow : growthRadius P ≤ r := le_trans (le_max_left _ _) hthr
  have hνthresh : max Rν 1 ≤ r := le_trans (le_max_right _ _) hthr
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  have hν1 : (1 : ℝ) ≤ ν := by
    have h1 : 1 ≤ centralIndex a r := hRν r (le_trans (le_max_left Rν 1) hνthresh)
    rw [hνdef]
    exact_mod_cast h1
  refine ⟨r, ?_, hr1, hν1, ?_⟩
  · have h1 : R ≤ y := le_trans (le_trans (le_max_left R 0) (le_max_left _ _)) hy
    have h2 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    rw [hrdef]
    linarith
  have hzr : ‖z‖ = r := hz
  set T : ℂ := deriv (coeffFun a) z / coeffFun a z with hTdef
  -- the two-sided Wiman estimate
  have hTbounds : ν ≤ 2 * (r * ‖T‖) ∧ r * ‖T‖ ≤ 2 * ν := by
    have hmd : z * deriv (coeffFun a) z / coeffFun a z = z * T := by
      rw [hTdef, mul_div_assoc]
    rw [hmd] at hdefect
    have hcast : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ = ν := by
      rw [hνdef, hrdef, Complex.norm_natCast]
    have hzT : ‖z * T‖ = r * ‖T‖ := by rw [norm_mul, hzr]
    have hup : ‖z * T‖
        ≤ ‖z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
          + ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ := by
      simpa using norm_add_le (z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ))
        (((centralIndex a (Real.exp y) : ℕ) : ℂ))
    have hlow : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
        ≤ ‖((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T‖ + ‖z * T‖ := by
      simpa using norm_add_le (((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T) (z * T)
    have hrev : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ) - z * T‖
        = ‖z * T - ((centralIndex a (Real.exp y) : ℕ) : ℂ)‖ := norm_sub_rev _ _
    rw [hrev, hcast, hzT] at hlow
    rw [hzT, hcast] at hup
    have hhalf : (1 : ℝ) / 2 * ((centralIndex a (Real.exp y) : ℕ) : ℝ) = ν / 2 := by
      rw [hνdef, hrdef]
      ring
    rw [hhalf] at hdefect
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hTlow, hTup⟩ := hTbounds
  have hfloor : κ * r ^ e ≤ ‖P.eval z‖ := by
    obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hAq (by rw [hzr]; exact hgrow)
    have hge := norm_eval_ge_of_large hAq hz1 hz2
    rw [hzr] at hge
    exact hge
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  have hmemStop : q ∈ Stop := by
    rw [hStopdef, Finset.mem_filter]
    exact ⟨hq, hqd⟩
  have hq2d : q.2 ≤ d := by
    have := hdeg q hq
    omega
  -- the chosen monomial has a floor after normalisation
  have hdom : κ * (r ^ (e + (d - q.2)) * ν ^ q.2)
      ≤ ‖P.eval z‖ * ‖T‖ ^ q.2 * (2 * r) ^ d := by
    have hrewrite : ‖P.eval z‖ * ‖T‖ ^ q.2 * (2 * r) ^ d
        = ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 * (2 ^ (d - q.2) * r ^ (d - q.2)) := by
      rw [mul_pow, show (2 : ℝ) ^ d = 2 ^ q.2 * 2 ^ (d - q.2) from by
          rw [← pow_add]; congr 1; omega,
        show r ^ d = r ^ q.2 * r ^ (d - q.2) from by rw [← pow_add]; congr 1; omega, mul_pow]
      ring
    have hstep : κ * r ^ e * ν ^ q.2 ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 := by
      calc κ * r ^ e * ν ^ q.2 ≤ ‖P.eval z‖ * ν ^ q.2 :=
            mul_le_mul_of_nonneg_right hfloor (by positivity)
        _ ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hTlow q.2)
              (norm_nonneg _)
    have htwo : (1 : ℝ) ≤ 2 ^ (d - q.2) := one_le_pow₀ (by norm_num)
    calc κ * (r ^ (e + (d - q.2)) * ν ^ q.2)
        = (κ * r ^ e * ν ^ q.2) * r ^ (d - q.2) := by rw [pow_add]; ring
      _ ≤ (‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2) * r ^ (d - q.2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ ≤ (‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2) * (2 ^ (d - q.2) * r ^ (d - q.2)) := by
          have hnn : (0 : ℝ) ≤ ‖P.eval z‖ * (2 * (r * ‖T‖)) ^ q.2 := by positivity
          have hle : r ^ (d - q.2) ≤ 2 ^ (d - q.2) * r ^ (d - q.2) := by
            nlinarith [pow_pos hrpos (d - q.2), htwo]
          exact mul_le_mul_of_nonneg_left hle hnn
      _ = ‖P.eval z‖ * ‖T‖ ^ q.2 * (2 * r) ^ d := hrewrite.symm
  -- every other top monomial has a ceiling after the same normalisation
  have hterm : ∀ p ∈ Stop.erase q,
      ‖(A p).eval z‖ * ‖T‖ ^ p.2 * (2 * r) ^ d
        ≤ Kc * 2 ^ (2 * d) * (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) := by
    intro p hp
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hp2d : p.2 ≤ d := by omega
    have hAp : ‖(A p).eval z‖ ≤ Kc * r ^ (A p).natDegree := by
      have h1 := norm_eval_le_of_one_le (p := A p) (z := z) (by rw [hzr]; exact hr1)
      rw [hzr] at h1
      have h2 : (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ Kc := hKcp p hpS
      have h3 : (0 : ℝ) ≤ r ^ (A p).natDegree := by positivity
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h3)
    have hsplit : (2 * r) ^ d = 2 ^ d * (r ^ p.2 * r ^ (d - p.2)) := by
      rw [mul_pow, show r ^ d = r ^ p.2 * r ^ (d - p.2) from by rw [← pow_add]; congr 1; omega]
    calc ‖(A p).eval z‖ * ‖T‖ ^ p.2 * (2 * r) ^ d
        = ‖(A p).eval z‖ * (r ^ p.2 * ‖T‖ ^ p.2) * (2 ^ d * r ^ (d - p.2)) := by
          rw [hsplit]; ring
      _ ≤ (Kc * r ^ (A p).natDegree) * (2 * ν) ^ p.2 * (2 ^ d * r ^ (d - p.2)) := by
          have hpow : r ^ p.2 * ‖T‖ ^ p.2 ≤ (2 * ν) ^ p.2 := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hTup p.2
          gcongr
      _ = Kc * 2 ^ (p.2 + d) * (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) := by
          rw [mul_pow, pow_add, pow_add]
          ring
      _ ≤ Kc * 2 ^ (2 * d) * (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) := by
          gcongr
          · norm_num
          · omega
  -- the relation, normalised
  have hsplitrel : ‖P.eval z‖ * ‖T‖ ^ q.2
      ≤ η + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
    have hsum : (A q).eval z * T ^ q.2
        + ∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2
        = ∑ p ∈ Stop, (A p).eval z * T ^ p.2 :=
      Finset.add_sum_erase _ (fun p => (A p).eval z * T ^ p.2) hmemStop
    have heq : P.eval z * T ^ q.2
        = (∑ p ∈ Stop, (A p).eval z * T ^ p.2)
          - ∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2 := by
      rw [← hsum, hPdef]
      ring
    have hbig : ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖ ≤ η := by
      rw [hStopdef, hTdef]
      exact htop
    calc ‖P.eval z‖ * ‖T‖ ^ q.2
        = ‖P.eval z * T ^ q.2‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖∑ p ∈ Stop, (A p).eval z * T ^ p.2‖
          + ‖∑ p ∈ Stop.erase q, (A p).eval z * T ^ p.2‖ := by
          rw [heq]
          exact norm_sub_le _ _
      _ ≤ η + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
          gcongr
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, norm_pow]
  have hmulnn : (0 : ℝ) ≤ (2 * r) ^ d := by positivity
  have hsumbound : (∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2) * (2 * r) ^ d
      ≤ Kc * 2 ^ (2 * d)
        * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hconst : η * (2 * r) ^ d = η * 2 ^ d * r ^ d := by rw [mul_pow]; ring
  have hchain : κ * (r ^ (e + (d - q.2)) * ν ^ q.2)
      ≤ η * 2 ^ d * r ^ d
        + Kc * 2 ^ (2 * d)
          * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2)) := by
    have h1 : ‖P.eval z‖ * ‖T‖ ^ q.2 * (2 * r) ^ d
        ≤ (η + ∑ p ∈ Stop.erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2) * (2 * r) ^ d :=
      mul_le_mul_of_nonneg_right hsplitrel hmulnn
    rw [add_mul, hconst] at h1
    linarith [hdom, hsumbound]
  exact hchain

end GaloisForLFunctions.HTGeometry
