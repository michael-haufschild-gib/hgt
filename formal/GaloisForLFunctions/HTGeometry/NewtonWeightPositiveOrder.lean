import GaloisForLFunctions.HTGeometry.TopSymbolWimanPlace
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# Newton faces of the top symbol at a Wiman place

At a Wiman--Valiron point the top symbol of an algebraic differential relation is arbitrarily small
while `z f'/f` is within a prescribed relative error of the central index.  Feeding the second fact
into the first, in both directions, turns the top symbol into a numerical inequality between the
central index and the radius.

Write the top-degree part as `∑_p A_p(z)·f^{p₁}·(f')^{p₂}` with `p₁ + p₂ = d`.  Normalising the
relation by `(2r)^d` — enough powers of the radius to clear every derivative factor — gives, for each
top monomial `q` with `A_q ≠ 0`, a floor for that monomial and a ceiling for all the others:

`‖lead A_q‖/2·r^{deg A_q + (d − q₂)}·ν^{q₂} ≤ η·2^d·r^d + K·∑_{p ≠ q} ν^{p₂}·r^{deg A_p + (d − p₂)}`.

This is `exists_radius_wimanFace`, and it carries no Newton hypothesis whatever.  The exponent
`deg A_p − p₂` is the Newton weight of a monomial, and each reading of the face inequality is an
arithmetic comparison of weights:

* if the pure monomial `A_d·f^d` has strictly maximal weight it cannot be cancelled unless the
  central index is at least a power of the radius — `κ·r ≤ ν(r)^d`, which is positive order;
* if a monomial with maximal derivative degree has strictly maximal weight, the same inequality read
  from below caps the central index instead;
* and when the capped monomial's coefficient degree is at least its derivative degree, the cap
  contradicts divergence of the central index, so no transcendental entire solution exists.

None of this needs a growth classification, an order, or convergence of `log ν/log r`.
-/

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

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

/-! ## The pure face -/

/-- **A dominant pure term forces the central index to grow like a power of the radius.**  For a
transcendental entire solution of an algebraic differential relation of total degree at most `d`
whose top-degree part contains the pure term `A_d·f^d` with `A_d ≠ 0`, if every other top-degree term
has strictly smaller Newton weight — `deg A_p + 1 ≤ deg A_d + p₂` — then there is a `κ > 0` with
`κ·r ≤ ν(r)^d` at arbitrarily large radii.

Reading the face inequality at `q = (d, 0)`: the pure monomial's floor is `κ₀ r^{deg A_d + d}`, while
the Newton hypothesis makes every other monomial lose a power of the radius against it, so the deficit
must be carried by the central index. -/
theorem exists_centralIndex_pow_ge_mul_radius
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
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
  obtain ⟨K, hK, hface⟩ :=
    exists_radius_wimanFace ha hn₀ htrans hdeg hrel hmem (by simp) hA0
      (η := κ0 / 2 ^ (d + 1)) (by positivity)
  set C : ℝ := K * (S.card : ℝ) + 1 with hCdef
  have hCpos : 0 < C := by
    have : (0 : ℝ) ≤ K * (S.card : ℝ) := by positivity
    rw [hCdef]; linarith
  refine ⟨κ0 / (2 * C), by positivity, ?_⟩
  intro R
  obtain ⟨r, hR, hr1, hν1, hface'⟩ := hface R
  refine ⟨r, hR, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  -- every other top monomial is a power of the radius behind the pure one
  have hterm : ∀ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
      (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r ≤ ν ^ d * r ^ (e0 + d) := by
    intro p hp
    have hpne : p ≠ ((d, 0) : ℕ × ℕ) := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hp2 : p.2 ≠ 0 := by
      intro h0
      exact hpne (Prod.ext (by omega) h0)
    have hp2d : p.2 ≤ d := by omega
    have hnewt : (A p).natDegree + 1 ≤ e0 + p.2 := by
      rw [he0def, hP0def]
      exact hNewton p hpS hpd hp2
    calc (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        = ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2) + 1) := by rw [pow_succ]; ring
      _ ≤ ν ^ d * r ^ (e0 + d) := by
          gcongr
          · exact hν1
          · omega
          · exact hr1
          · omega
  have hsum : (∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
      ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
      ≤ (S.card : ℝ) * (ν ^ d * r ^ (e0 + d)) := by
    rw [Finset.sum_mul]
    have hcardle : ((Stop.erase ((d, 0) : ℕ × ℕ)).card : ℝ) ≤ (S.card : ℝ) := by
      have h1 : (Stop.erase ((d, 0) : ℕ × ℕ)).card ≤ S.card := by
        refine Finset.card_le_card fun x hx => ?_
        have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
        rw [hStopdef] at hx1
        exact (Finset.mem_filter.mp hx1).1
      exact_mod_cast h1
    have hle := Finset.sum_le_card_nsmul (Stop.erase ((d, 0) : ℕ × ℕ))
      (fun p => (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r)
      (ν ^ d * r ^ (e0 + d)) hterm
    rw [nsmul_eq_mul] at hle
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle (by positivity))
  -- the free constant is absorbed by the floor
  have hconst : κ0 / 2 ^ (d + 1) * 2 ^ d * r ^ d ≤ κ0 / 2 * r ^ (e0 + d) := by
    have hpowle : r ^ d ≤ r ^ (e0 + d) := pow_le_pow_right₀ hr1 (by omega)
    have hcoef : κ0 / 2 ^ (d + 1) * 2 ^ d = κ0 / 2 := by
      rw [pow_succ]
      field_simp
      ring
    rw [hcoef]
    exact mul_le_mul_of_nonneg_left hpowle (by positivity)
  have hpure : κ0 * (r ^ (e0 + (d - 0)) * ν ^ (0 : ℕ)) = κ0 * r ^ (e0 + d) := by
    simp
  rw [hpure] at hface'
  -- the resulting comparison, cleared of the common power
  have hstep : κ0 / 2 * r ^ (e0 + d) * r ≤ K * ((S.card : ℝ) * (ν ^ d * r ^ (e0 + d))) := by
    have h1 : κ0 * r ^ (e0 + d) * r
        ≤ (κ0 / 2 * r ^ (e0 + d)) * r
          + (K * ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
              ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r := by
      have := mul_le_mul_of_nonneg_right hface' hrpos.le
      nlinarith [mul_le_mul_of_nonneg_right hconst hrpos.le, this]
    have h2 : (K * ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
        ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        ≤ K * ((S.card : ℝ) * (ν ^ d * r ^ (e0 + d))) := by
      have := mul_le_mul_of_nonneg_left hsum hK.le
      calc (K * ∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
            ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
          = K * ((∑ p ∈ Stop.erase ((d, 0) : ℕ × ℕ),
              ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) := by ring
        _ ≤ K * ((S.card : ℝ) * (ν ^ d * r ^ (e0 + d))) := this
    nlinarith [h1, h2]
  have hpowpos : (0 : ℝ) < r ^ (e0 + d) := by positivity
  have hdiv : κ0 / 2 * r ≤ K * (S.card : ℝ) * ν ^ d := by
    refine le_of_mul_le_mul_right ?_ hpowpos
    calc κ0 / 2 * r * r ^ (e0 + d) = κ0 / 2 * r ^ (e0 + d) * r := by ring
      _ ≤ K * ((S.card : ℝ) * (ν ^ d * r ^ (e0 + d))) := hstep
      _ = K * (S.card : ℝ) * ν ^ d * r ^ (e0 + d) := by ring
  have hCν : K * (S.card : ℝ) * ν ^ d ≤ C * ν ^ d := by
    have hle : K * (S.card : ℝ) ≤ C := by rw [hCdef]; linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
  calc κ0 * r = 2 * (κ0 / 2 * r) := by ring
    _ ≤ 2 * (C * ν ^ d) := by linarith
    _ = ν ^ d * (2 * C) := by ring

/-! ## The derivative face -/

/-- **A dominant term of maximal derivative degree caps the central index.**  If the top-degree part
has a monomial `q` carrying at least as many derivative factors as every other top monomial and of
strictly maximal Newton weight, then that monomial cannot be cancelled: at arbitrarily large radii

`ν(r)^{q₂}·r^{deg A_q + 1} ≤ C·r^{q₂ + 1}`.

This is the face inequality read at `q`.  Having no fewer derivative factors than its competitors,
`q` cannot be overtaken through the central index, so the whole deficit falls on the radius. -/
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
  set e : ℕ := (A q).natDegree with hedef
  have hlc : 0 < ‖(A q).leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAq)
  set κ : ℝ := ‖(A q).leadingCoeff‖ / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hq2d : q.2 ≤ d := by have := hdeg q hq; omega
  obtain ⟨K, hK, hface⟩ :=
    exists_radius_wimanFace ha hn₀ htrans hdeg hrel hq hqd hAq (η := 1) one_pos
  refine ⟨2 ^ (d + 1) / κ, by positivity, ?_⟩
  intro R
  obtain ⟨r, hR, hr1, hν1, hface'⟩ :=
    hface (max R (2 * K * (S.card : ℝ) / κ))
  have hRr : R ≤ r := le_trans (le_max_left _ _) hR
  have hthr : 2 * K * (S.card : ℝ) / κ ≤ r := le_trans (le_max_right _ _) hR
  refine ⟨r, hRr, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  set E : ℕ := e + (d - q.2) with hEdef
  -- every other top monomial is a power of the radius behind `q`
  have hterm : ∀ p ∈ Stop.erase q,
      (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r ≤ ν ^ q.2 * r ^ E := by
    intro p hp
    have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hp2q : p.2 ≤ q.2 := hmaxT p hpS hpd
    have hnewt : (A p).natDegree + (q.2 - p.2) + 1 ≤ e := by
      rw [hedef]
      exact hNewton p hpS hpd hpne
    calc (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        = ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2) + 1) := by rw [pow_succ]; ring
      _ ≤ ν ^ q.2 * r ^ E := by
          rw [hEdef]
          gcongr
          · exact hν1
          · exact hr1
          · omega
  have hsum : (∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
      ≤ (S.card : ℝ) * (ν ^ q.2 * r ^ E) := by
    rw [Finset.sum_mul]
    have hcardle : ((Stop.erase q).card : ℝ) ≤ (S.card : ℝ) := by
      have h1 : (Stop.erase q).card ≤ S.card := by
        refine Finset.card_le_card fun x hx => ?_
        have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
        rw [hStopdef] at hx1
        exact (Finset.mem_filter.mp hx1).1
      exact_mod_cast h1
    have hle := Finset.sum_le_card_nsmul (Stop.erase q)
      (fun p => (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r)
      (ν ^ q.2 * r ^ E) hterm
    rw [nsmul_eq_mul] at hle
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle (by positivity))
  -- the threshold absorbs the competitors into half the floor
  have habsorb : K * ((S.card : ℝ) * (ν ^ q.2 * r ^ E)) ≤ κ / 2 * (r ^ E * ν ^ q.2 * r) := by
    have hcst : 2 * K * (S.card : ℝ) ≤ κ * r := by
      rw [div_le_iff₀ hκ] at hthr
      linarith
    have hnn : (0 : ℝ) ≤ ν ^ q.2 * r ^ E := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcst hnn]
  have hmain : κ * (r ^ E * ν ^ q.2) * r
      ≤ 1 * 2 ^ d * r ^ d * r + κ / 2 * (r ^ E * ν ^ q.2 * r) := by
    have h1 := mul_le_mul_of_nonneg_right hface' hrpos.le
    have h2 : (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        ≤ K * ((S.card : ℝ) * (ν ^ q.2 * r ^ E)) := by
      calc (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
          = K * ((∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) := by
            ring
        _ ≤ K * ((S.card : ℝ) * (ν ^ q.2 * r ^ E)) := mul_le_mul_of_nonneg_left hsum hK.le
    rw [add_mul] at h1
    linarith [h1, h2, habsorb]
  have hhalf : κ / 2 * (r ^ E * ν ^ q.2 * r) ≤ 2 ^ d * r ^ (d + 1) := by
    have hrw : (1 : ℝ) * 2 ^ d * r ^ d * r = 2 ^ d * r ^ (d + 1) := by rw [pow_succ]; ring
    rw [hrw] at hmain
    have hz : κ * (r ^ E * ν ^ q.2) * r = κ * (r ^ E * ν ^ q.2 * r) := by ring
    rw [hz] at hmain
    linarith
  -- reading off the stated inequality
  have hEr : r ^ E * ν ^ q.2 * r = (ν ^ q.2 * r ^ (e + 1)) * r ^ (d - q.2) := by
    rw [hEdef, pow_add, pow_add]
    ring
  have hdr : (2 : ℝ) ^ d * r ^ (d + 1) = (2 ^ (d + 1) / κ * r ^ (q.2 + 1)) * (κ / 2 * r ^ (d - q.2)) := by
    rw [show d + 1 = (q.2 + 1) + (d - q.2) from by omega, pow_add]
    field_simp
    ring
  rw [hEr, hdr] at hhalf
  have hpowpos : (0 : ℝ) < r ^ (d - q.2) := by positivity
  refine le_of_mul_le_mul_right ?_ hpowpos
  calc ν ^ q.2 * r ^ (e + 1) * r ^ (d - q.2)
      = 2 / κ * (κ / 2 * ((ν ^ q.2 * r ^ (e + 1)) * r ^ (d - q.2))) := by
        field_simp
    _ ≤ 2 / κ * ((2 ^ (d + 1) / κ * r ^ (q.2 + 1)) * (κ / 2 * r ^ (d - q.2))) := by
        have h2κ : (0 : ℝ) < 2 / κ := by positivity
        exact mul_le_mul_of_nonneg_left hhalf h2κ.le
    _ = 2 ^ (d + 1) / κ * r ^ (q.2 + 1) * r ^ (d - q.2) := by
        field_simp
        ring

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

end GaloisForLFunctions.HTGeometry
