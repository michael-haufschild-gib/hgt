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
`deg A_p − p₂` is the Newton weight of a monomial, and every further statement here is an arithmetic
comparison of weights inside that one inequality.

Applying the weight comparison once collapses the competitors into a single term
(`exists_radius_weightCollapse`): with `E = deg A_q + (d − q₂)` and `P` any bound for the competitors'
derivative degrees,

`ν^{q₂}·r^{E+1} ≤ η·r^{d+1} + C·ν^P·r^E`  for every `η > 0`, with `C` independent of `η`.

Both readings below are two-line consequences of that, and between them they cover every case of a
strictly maximal weight.

The first is `exists_centralIndex_pow_mul_radius_le`: a monomial `q` of strictly maximal weight with
`q₂ ≤ deg A_q` pins the central index by

`ν(r)^{q₂}·r ≤ C·ν(r)^P`,

`P` any bound for the derivative degrees of the competitors.  Its two extremes are the classical
alternatives:

* at the pure monomial `A_d·f^d` this is `κ·r ≤ ν(r)^d` — positive order;
* when no competitor has more derivative factors than `q`, the central index cancels and the radius
  is bounded, which is impossible: there is no transcendental entire solution at all.

The second, `centralIndex_pow_mul_pow_le_of_dominant_derivative_term`, covers the remaining case
`deg A_q < q₂`, where the residue of the top symbol is no longer absorbed by the floor and the
conclusion is a cap, `ν^{q₂}·r^{deg A_q + 1} ≤ 2·r^{q₂+1}`, instead.

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
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
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
  intro η hη R
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

/-! ## Collapsing the competitors -/

/-- **The weight comparison, collapsed.**  If the top-degree monomial `q` has strictly maximal Newton
weight and `P` bounds the derivative degrees of its competitors, the face inequality collapses to a
two-term comparison in which the free constant survives:

`ν^{q₂}·r^{E+1} ≤ η·r^{d+1} + C·ν^P·r^E`,  `E = deg A_q + (d − q₂)`,

for every `η > 0` at arbitrarily large radii, with `C` independent of `η`.  Each competitor has lost
one power of the radius against `q` and can recover it only through the central index; the first term
is the residue of the top symbol itself, and its coefficient is free. -/
theorem exists_radius_weightCollapse
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hweight : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2))
    {P : ℕ} (hP : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q → p.2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
      1 ≤ ((centralIndex a r : ℕ) : ℝ) ∧
      ((centralIndex a r : ℕ) : ℝ) ^ q.2 * r ^ ((A q).natDegree + (d - q.2) + 1)
        ≤ η * r ^ (d + 1)
          + C * (((centralIndex a r : ℕ) : ℝ) ^ P * r ^ ((A q).natDegree + (d - q.2))) := by
  classical
  have hlc : 0 < ‖(A q).leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAq)
  have hκ : 0 < ‖(A q).leadingCoeff‖ / 2 := by linarith
  obtain ⟨K, hK, hface⟩ := exists_radius_wimanFace ha hn₀ htrans hdeg hrel hq hqd hAq
  refine ⟨K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) + 1, by positivity, ?_⟩
  intro η hη R
  obtain ⟨r, hR, hr1, hν1, hface'⟩ :=
    hface (η * (‖(A q).leadingCoeff‖ / 2) / 2 ^ d) (by positivity) R
  refine ⟨r, hR, hr1, hν1, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  set E : ℕ := (A q).natDegree + (d - q.2) with hEdef
  -- each competitor loses a power of the radius
  have hterm : ∀ p ∈ Stop.erase q,
      (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r ≤ ν ^ P * r ^ E := by
    intro p hp
    have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have h1 : ν ^ p.2 ≤ ν ^ P := pow_le_pow_right₀ hν1 (hP p hpS hpd hpne)
    have h2 : r ^ ((A p).natDegree + (d - p.2) + 1) ≤ r ^ E :=
      pow_le_pow_right₀ hr1 (by rw [hEdef]; exact hweight p hpS hpd hpne)
    calc (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        = ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2) + 1) := by rw [pow_succ]; ring
      _ ≤ ν ^ P * r ^ E := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hsum : (∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
      ≤ (S.card : ℝ) * (ν ^ P * r ^ E) := by
    rw [Finset.sum_mul]
    have hcardle : ((Stop.erase q).card : ℝ) ≤ (S.card : ℝ) := by
      have h1 : (Stop.erase q).card ≤ S.card := by
        refine Finset.card_le_card fun x hx => ?_
        have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
        rw [hStopdef] at hx1
        exact (Finset.mem_filter.mp hx1).1
      exact_mod_cast h1
    have hle := Finset.sum_le_card_nsmul (Stop.erase q)
      (fun p => (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) (ν ^ P * r ^ E) hterm
    rw [nsmul_eq_mul] at hle
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle (by positivity))
  -- the normalised relation, multiplied by the radius
  have hmain : ‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1))
      ≤ η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1)
        + K * ((S.card : ℝ) * (ν ^ P * r ^ E)) := by
    have h1 := mul_le_mul_of_nonneg_right hface' hrpos.le
    rw [add_mul] at h1
    have h2 : (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        ≤ K * ((S.card : ℝ) * (ν ^ P * r ^ E)) := by
      calc (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
          = K * ((∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) := by
            ring
        _ ≤ K * ((S.card : ℝ) * (ν ^ P * r ^ E)) := mul_le_mul_of_nonneg_left hsum hK.le
    have h3 : ‖(A q).leadingCoeff‖ / 2 * (r ^ E * ν ^ q.2) * r
        = ‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1)) := by rw [pow_succ]; ring
    rw [hEdef] at h3
    rw [h3] at h1
    have h4 : η * (‖(A q).leadingCoeff‖ / 2) / 2 ^ d * 2 ^ d * r ^ d * r
        = η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1) := by
      rw [pow_succ]
      field_simp
    rw [h4] at h1
    linarith
  -- dividing by the leading constant
  have hdiv : ν ^ q.2 * r ^ (E + 1)
      ≤ η * r ^ (d + 1)
        + K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * (ν ^ P * r ^ E) := by
    have hmul := mul_le_mul_of_nonneg_left hmain
      (le_of_lt (by positivity : (0 : ℝ) < (‖(A q).leadingCoeff‖ / 2)⁻¹))
    have e1 : (‖(A q).leadingCoeff‖ / 2)⁻¹ * (‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1)))
        = ν ^ q.2 * r ^ (E + 1) := by field_simp
    have e2 : (‖(A q).leadingCoeff‖ / 2)⁻¹
          * (η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1)
            + K * ((S.card : ℝ) * (ν ^ P * r ^ E)))
        = η * r ^ (d + 1)
          + K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * (ν ^ P * r ^ E) := by
      field_simp
    rw [e1, e2] at hmul
    exact hmul
  have hCle : K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * (ν ^ P * r ^ E)
      ≤ (K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) + 1) * (ν ^ P * r ^ E) := by
    have hnn : (0 : ℝ) ≤ ν ^ P * r ^ E := by positivity
    nlinarith
  rw [hEdef]
  linarith [hdiv, hCle]

/-! ## The general reading of a face -/

/-- **A strictly maximal Newton weight pins the central index.**  Let `q` be a top-degree monomial
with `A_q ≠ 0` whose Newton weight strictly exceeds that of every other top-degree monomial, and
suppose its coefficient degree is at least its derivative degree.  If `P` bounds the derivative
degrees of the competing monomials, then at arbitrarily large radii

`ν(r)^{q₂}·r ≤ C·ν(r)^P`.

This is the face inequality read at `q` with a small free constant: the constant term is absorbed by
the floor because `q₂ ≤ deg A_q`, and each competitor loses exactly one power of the radius, which it
can only recover through the central index.

Both extreme cases follow.  With `P ≤ q₂` the central index cancels and the radius is bounded, which
is impossible: no such solution exists.  With `q₂ = 0` it reads `r ≤ C·ν^P`, positive order. -/
theorem exists_centralIndex_pow_mul_radius_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hdegq : q.2 ≤ (A q).natDegree)
    (hweight : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2))
    {P : ℕ} (hP : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q → p.2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
      1 ≤ ((centralIndex a r : ℕ) : ℝ) ∧
      ((centralIndex a r : ℕ) : ℝ) ^ q.2 * r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ P := by
  classical
  have hq2d : q.2 ≤ d := by have := hdeg q hq; omega
  obtain ⟨C, hC, hcol⟩ :=
    exists_radius_weightCollapse ha hn₀ htrans hdeg hrel hq hqd hAq hweight hP
  refine ⟨2 * C, by positivity, ?_⟩
  intro R
  obtain ⟨r, hR, hr1, hν1, hb⟩ := hcol (1 / 2) (by norm_num) R
  refine ⟨r, hR, hr1, hν1, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set E : ℕ := (A q).natDegree + (d - q.2) with hEdef
  have hνq : (1 : ℝ) ≤ ν ^ q.2 := one_le_pow₀ hν1
  -- the free term is absorbed by the floor
  have habsorb : (1 : ℝ) / 2 * r ^ (d + 1) ≤ 1 / 2 * (ν ^ q.2 * r ^ (E + 1)) := by
    have h1 : r ^ (d + 1) ≤ r ^ (E + 1) := pow_le_pow_right₀ hr1 (by rw [hEdef]; omega)
    have h2 : r ^ (E + 1) ≤ ν ^ q.2 * r ^ (E + 1) := by
      nlinarith [pow_pos hrpos (E + 1)]
    linarith
  have hhalf : (1 : ℝ) / 2 * (ν ^ q.2 * r ^ (E + 1)) ≤ C * (ν ^ P * r ^ E) := by
    rw [hEdef] at hb ⊢
    linarith [hb, habsorb]
  have hpowpos : (0 : ℝ) < r ^ E := by positivity
  refine le_of_mul_le_mul_right ?_ hpowpos
  calc ν ^ q.2 * r * r ^ E = 2 * (1 / 2 * (ν ^ q.2 * r ^ (E + 1))) := by rw [pow_succ]; ring
    _ ≤ 2 * (C * (ν ^ P * r ^ E)) := by linarith
    _ = 2 * C * ν ^ P * r ^ E := by ring

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
  obtain ⟨C, hC, hbound⟩ :=
    exists_centralIndex_pow_mul_radius_le ha hn₀ htrans hdeg hrel hmem (by simp) hA0
      (by simp)
      (fun p hpS hpd hpne => by
        have hp2 : p.2 ≠ 0 := fun h0 => hpne (Prod.ext (by omega) h0)
        have hp2d : p.2 ≤ d := by omega
        have := hNewton p hpS hpd hp2
        simp only []
        omega)
      (P := d) (fun p hpS _ _ => by have := hdeg p hpS; omega)
  refine ⟨1 / C, by positivity, ?_⟩
  intro R
  obtain ⟨r, hR, hr1, _, hb⟩ := hbound R
  refine ⟨r, hR, ?_⟩
  rw [show ((d, 0) : ℕ × ℕ).2 = 0 from rfl, pow_zero, one_mul] at hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  linarith

/-! ## The derivative face -/

/-- **A dominant term whose coefficient degree is below its derivative degree caps the central
index.**  This is the reading of the face inequality left over when `deg A_q < q₂`, so that the
residue of the top symbol is no longer absorbed by the floor.  With no competitor carrying more
derivative factors, the whole deficit falls on the radius:

`ν(r)^{q₂}·r^{deg A_q + 1} ≤ 2·r^{q₂ + 1}`. -/
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
  have hq2d : q.2 ≤ d := by have := hdeg q hq; omega
  obtain ⟨C, hC, hcol⟩ :=
    exists_radius_weightCollapse ha hn₀ htrans hdeg hrel hq hqd hAq
      (fun p hpS hpd hpne => by
        have h1 := hNewton p hpS hpd hpne
        have h2 : p.2 ≤ q.2 := hmaxT p hpS hpd
        omega)
      (P := q.2) (fun p hpS hpd _ => hmaxT p hpS hpd)
  refine ⟨2, by norm_num, ?_⟩
  intro R
  obtain ⟨r, hR, hr1, hν1, hb⟩ := hcol 1 one_pos (max R (2 * C))
  have hRr : R ≤ r := le_trans (le_max_left _ _) hR
  have hthr : 2 * C ≤ r := le_trans (le_max_right _ _) hR
  refine ⟨r, hRr, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set E : ℕ := (A q).natDegree + (d - q.2) with hEdef
  -- the threshold absorbs the competitors into half the floor
  have habsorb : C * (ν ^ q.2 * r ^ E) ≤ 1 / 2 * (ν ^ q.2 * r ^ (E + 1)) := by
    have hnn : (0 : ℝ) ≤ ν ^ q.2 * r ^ E := by positivity
    have hstep : C * (ν ^ q.2 * r ^ E) ≤ 1 / 2 * r * (ν ^ q.2 * r ^ E) := by
      nlinarith [hnn, hthr]
    calc C * (ν ^ q.2 * r ^ E) ≤ 1 / 2 * r * (ν ^ q.2 * r ^ E) := hstep
      _ = 1 / 2 * (ν ^ q.2 * r ^ (E + 1)) := by rw [pow_succ]; ring
  have hcap : ν ^ q.2 * r ^ (E + 1) ≤ 2 * r ^ (d + 1) := by linarith [hb, habsorb]
  -- dividing out the common power
  have hEsplit : ν ^ q.2 * r ^ (E + 1)
      = (ν ^ q.2 * r ^ ((A q).natDegree + 1)) * r ^ (d - q.2) := by
    have hp : r ^ (E + 1) = r ^ ((A q).natDegree + 1) * r ^ (d - q.2) := by
      rw [← pow_add, hEdef]
      congr 1
      omega
    rw [hp]
    ring
  have hdsplit : (2 : ℝ) * r ^ (d + 1) = (2 * r ^ (q.2 + 1)) * r ^ (d - q.2) := by
    have hp : r ^ (d + 1) = r ^ (q.2 + 1) * r ^ (d - q.2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp]
    ring
  rw [hEsplit, hdsplit] at hcap
  exact le_of_mul_le_mul_right hcap (by positivity)

/-- **No transcendental entire solution when the dominant monomial also has the larger coefficient
degree.**  If a top-degree monomial has strictly maximal Newton weight, no fewer derivative factors
than any competitor, and coefficient degree at least its derivative degree, then the pinning
inequality reads `ν^{q₂}·r ≤ C·ν^{q₂}`: the central index cancels, the radius is bounded, and that is
impossible. -/
theorem not_transcendental_of_dominant_derivative_term
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hmaxT : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ q.2)
    (hNewton : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (q.2 - p.2) + 1 ≤ (A q).natDegree)
    (hdegq : q.2 ≤ (A q).natDegree) : False := by
  classical
  have hq2d : q.2 ≤ d := by have := hdeg q hq; omega
  obtain ⟨C, hC, hbound⟩ :=
    exists_centralIndex_pow_mul_radius_le ha hn₀ htrans hdeg hrel hq hqd hAq hdegq
      (fun p hpS hpd hpne => by
        have h1 := hNewton p hpS hpd hpne
        have h2 : p.2 ≤ q.2 := hmaxT p hpS hpd
        omega)
      (P := q.2) (fun p hpS hpd _ => hmaxT p hpS hpd)
  obtain ⟨r, hR, hr1, hν1, hb⟩ := hbound (C + 1)
  have hνpow : (1 : ℝ) ≤ ((centralIndex a r : ℕ) : ℝ) ^ q.2 := one_le_pow₀ hν1
  have hrle : r ≤ C := by
    refine le_of_mul_le_mul_left ?_ (lt_of_lt_of_le zero_lt_one hνpow)
    calc ((centralIndex a r : ℕ) : ℝ) ^ q.2 * r
        ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ q.2 := hb
      _ = ((centralIndex a r : ℕ) : ℝ) ^ q.2 * C := by ring
  linarith

/-! ## Ties at the maximal weight

A maximal weight need not be attained once.  Among the monomials attaining it, the one with the most
derivative factors dominates the others as soon as the central index is large, because the tied terms
differ exactly by powers of `ν`.  In the top-degree set a monomial is determined by its derivative
degree, so that dominant monomial is always unique — the hypothesis below is not a restriction but a
choice of `q`.

This is the reading that no longer needs the weight to be *strictly* maximal, and it is the one that
yields positive order for the general first-order equation. -/

/-- **The collapse at a tie.**  With `q` of maximal Newton weight and of strictly largest derivative
degree among the monomials attaining that weight, the competitors split into two groups: the tied ones
lose a power of the central index, the rest lose a power of the radius. -/
theorem exists_radius_tieCollapse
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (htie : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2) ∨
        ((A p).natDegree + (d - p.2) = (A q).natDegree + (d - q.2) ∧ p.2 + 1 ≤ q.2))
    {P : ℕ} (hP : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q → p.2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
      1 ≤ ((centralIndex a r : ℕ) : ℝ) ∧
      ((centralIndex a r : ℕ) : ℝ) ^ q.2 * r ^ ((A q).natDegree + (d - q.2) + 1)
        ≤ η * r ^ (d + 1)
          + C * (((centralIndex a r : ℕ) : ℝ) ^ (q.2 - 1)
                  * r ^ ((A q).natDegree + (d - q.2) + 1)
                + ((centralIndex a r : ℕ) : ℝ) ^ P * r ^ ((A q).natDegree + (d - q.2))) := by
  classical
  have hlc : 0 < ‖(A q).leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAq)
  have hκ : 0 < ‖(A q).leadingCoeff‖ / 2 := by linarith
  obtain ⟨K, hK, hface⟩ := exists_radius_wimanFace ha hn₀ htrans hdeg hrel hq hqd hAq
  refine ⟨K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) + 1, by positivity, ?_⟩
  intro η hη R
  obtain ⟨r, hR, hr1, hν1, hface'⟩ :=
    hface (η * (‖(A q).leadingCoeff‖ / 2) / 2 ^ d) (by positivity) R
  refine ⟨r, hR, hr1, hν1, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set Stop : Finset (ℕ × ℕ) := S.filter (fun p => p.1 + p.2 = d) with hStopdef
  set E : ℕ := (A q).natDegree + (d - q.2) with hEdef
  set B : ℝ := ν ^ (q.2 - 1) * r ^ (E + 1) + ν ^ P * r ^ E with hBdef
  have hterm : ∀ p ∈ Stop.erase q,
      (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r ≤ B := by
    intro p hp
    have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hpStop : p ∈ Stop := (Finset.mem_erase.mp hp).2
    have hpF : p ∈ S.filter (fun t : ℕ × ℕ => t.1 + t.2 = d) := by
      rw [hStopdef] at hpStop
      exact hpStop
    have hpS : p ∈ S := (Finset.mem_filter.mp hpF).1
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hpF).2
    have hrew : (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        = ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2) + 1) := by rw [pow_succ]; ring
    have hnn1 : (0 : ℝ) ≤ ν ^ (q.2 - 1) * r ^ (E + 1) := by positivity
    have hnn2 : (0 : ℝ) ≤ ν ^ P * r ^ E := by positivity
    rcases htie p hpS hpd hpne with hstrict | ⟨heq, hlt⟩
    · have h1 : ν ^ p.2 ≤ ν ^ P := pow_le_pow_right₀ hν1 (hP p hpS hpd hpne)
      have h2 : r ^ ((A p).natDegree + (d - p.2) + 1) ≤ r ^ E :=
        pow_le_pow_right₀ hr1 (by rw [hEdef]; exact hstrict)
      rw [hrew, hBdef]
      have := mul_le_mul h1 h2 (by positivity) (by positivity)
      linarith
    · have h1 : ν ^ p.2 ≤ ν ^ (q.2 - 1) := pow_le_pow_right₀ hν1 (by omega)
      have h2 : r ^ ((A p).natDegree + (d - p.2) + 1) ≤ r ^ (E + 1) :=
        pow_le_pow_right₀ hr1 (by rw [hEdef]; omega)
      rw [hrew, hBdef]
      have := mul_le_mul h1 h2 (by positivity) (by positivity)
      linarith
  have hsum : (∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
      ≤ (S.card : ℝ) * B := by
    rw [Finset.sum_mul]
    have hcardle : ((Stop.erase q).card : ℝ) ≤ (S.card : ℝ) := by
      have h1 : (Stop.erase q).card ≤ S.card := by
        refine Finset.card_le_card fun x hx => ?_
        have hx1 : x ∈ Stop := (Finset.mem_erase.mp hx).2
        rw [hStopdef] at hx1
        exact (Finset.mem_filter.mp hx1).1
      exact_mod_cast h1
    have hle := Finset.sum_le_card_nsmul (Stop.erase q)
      (fun p => (ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) B hterm
    rw [nsmul_eq_mul] at hle
    have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
    exact le_trans hle (mul_le_mul_of_nonneg_right hcardle hBnn)
  have hmain : ‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1))
      ≤ η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1) + K * ((S.card : ℝ) * B) := by
    have h1 := mul_le_mul_of_nonneg_right hface' hrpos.le
    rw [add_mul] at h1
    have h2 : (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
        ≤ K * ((S.card : ℝ) * B) := by
      calc (K * ∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r
          = K * ((∑ p ∈ Stop.erase q, ν ^ p.2 * r ^ ((A p).natDegree + (d - p.2))) * r) := by
            ring
        _ ≤ K * ((S.card : ℝ) * B) := mul_le_mul_of_nonneg_left hsum hK.le
    have h3 : ‖(A q).leadingCoeff‖ / 2 * (r ^ E * ν ^ q.2) * r
        = ‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1)) := by rw [pow_succ]; ring
    rw [hEdef] at h3
    rw [h3] at h1
    have h4 : η * (‖(A q).leadingCoeff‖ / 2) / 2 ^ d * 2 ^ d * r ^ d * r
        = η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1) := by
      rw [pow_succ]
      field_simp
    rw [h4] at h1
    linarith
  have hdiv : ν ^ q.2 * r ^ (E + 1)
      ≤ η * r ^ (d + 1) + K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * B := by
    have hmul := mul_le_mul_of_nonneg_left hmain
      (le_of_lt (by positivity : (0 : ℝ) < (‖(A q).leadingCoeff‖ / 2)⁻¹))
    have e1 : (‖(A q).leadingCoeff‖ / 2)⁻¹ * (‖(A q).leadingCoeff‖ / 2 * (ν ^ q.2 * r ^ (E + 1)))
        = ν ^ q.2 * r ^ (E + 1) := by field_simp
    have e2 : (‖(A q).leadingCoeff‖ / 2)⁻¹
          * (η * (‖(A q).leadingCoeff‖ / 2) * r ^ (d + 1) + K * ((S.card : ℝ) * B))
        = η * r ^ (d + 1) + K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * B := by
      field_simp
    rw [e1, e2] at hmul
    exact hmul
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hCle : K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) * B
      ≤ (K * (S.card : ℝ) / (‖(A q).leadingCoeff‖ / 2) + 1) * B := by nlinarith
  linarith [hdiv, hCle]

/-- **Positive order at a tie.**  If the monomial `q` of maximal Newton weight and largest derivative
degree among the tied ones satisfies `1 ≤ q₂ ≤ deg A_q`, and `P` bounds the derivative degrees of the
competitors, then at arbitrarily large radii

`r ≤ C·ν(r)^{P − q₂}`.

The tied competitors cost one power of the central index and the others one power of the radius, so
dividing the collapsed inequality by `ν^{q₂−1}r^E` leaves `ν·r ≤ C(r + ν^{P+1−q₂})`; divergence of the
central index kills the first term, and what remains is the stated bound.

For `P ≤ q₂` it reads `r ≤ C` and there is no such solution; for `q₂ < P` it is positive order with
exponent `1/(P − q₂)`. -/
theorem exists_radius_le_centralIndex_pow
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hq1 : 1 ≤ q.2) (hdegq : q.2 ≤ (A q).natDegree)
    (htie : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2) ∨
        ((A p).natDegree + (d - p.2) = (A q).natDegree + (d - q.2) ∧ p.2 + 1 ≤ q.2))
    {P : ℕ} (hP : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q → p.2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ 1 ≤ ((centralIndex a r : ℕ) : ℝ) ∧
      r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ (P - q.2) := by
  classical
  have hq2d : q.2 ≤ d := by have := hdeg q hq; omega
  obtain ⟨C, hC, hcol⟩ :=
    exists_radius_tieCollapse ha hn₀ htrans hdeg hrel hq hqd hAq htie hP
  refine ⟨4 * C, by positivity, ?_⟩
  intro R
  -- past this radius the central index exceeds every competitor's contribution
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 4 * C ≤ (M : ℝ) := ⟨⌈4 * C⌉₊, Nat.le_ceil _⟩
  obtain ⟨R₀, hR₀⟩ := tendsto_atTop_atTop.mp (tendsto_centralIndex_atTop ha htrans) (M + 1)
  obtain ⟨r, hR, hr1, hν1, hb⟩ := hcol (1 / 2) (by norm_num) (max R R₀)
  have hRr : R ≤ r := le_trans (le_max_left _ _) hR
  refine ⟨r, hRr, hν1, ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  set ν : ℝ := ((centralIndex a r : ℕ) : ℝ) with hνdef
  set E : ℕ := (A q).natDegree + (d - q.2) with hEdef
  have hνbig : 4 * C < ν := by
    have h1 : M + 1 ≤ centralIndex a r := hR₀ r (le_trans (le_max_right _ _) hR)
    have h2 : ((M : ℝ) + 1) ≤ ν := by rw [hνdef]; exact_mod_cast h1
    linarith
  have hνpos : (0 : ℝ) < ν := by linarith
  -- the free term is absorbed by the floor
  have habsorb : (1 : ℝ) / 2 * r ^ (d + 1) ≤ 1 / 2 * (ν ^ q.2 * r ^ (E + 1)) := by
    have h1 : r ^ (d + 1) ≤ r ^ (E + 1) := pow_le_pow_right₀ hr1 (by rw [hEdef]; omega)
    have h2 : r ^ (E + 1) ≤ ν ^ q.2 * r ^ (E + 1) := by
      have : (1 : ℝ) ≤ ν ^ q.2 := one_le_pow₀ hν1
      nlinarith [pow_pos hrpos (E + 1)]
    linarith
  have hhalf : (1 : ℝ) / 2 * (ν ^ q.2 * r ^ (E + 1))
      ≤ C * (ν ^ (q.2 - 1) * r ^ (E + 1) + ν ^ P * r ^ E) := by
    rw [hEdef] at hb habsorb ⊢
    linarith
  -- dividing out the common factor
  have hsplit : ν ^ q.2 * r ^ (E + 1) = ν * (ν ^ (q.2 - 1) * r ^ E) * r := by
    have hν : ν ^ q.2 = ν * ν ^ (q.2 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hν, pow_succ]
    ring
  have hPle : ν ^ P ≤ ν ^ (q.2 - 1) * ν ^ (P + 1 - q.2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hν1 (by omega)
  have hmle : ν ^ (P + 1 - q.2) ≤ ν ^ (P - q.2) * ν := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hν1 (by omega)
  have hfactorpos : (0 : ℝ) < ν ^ (q.2 - 1) * r ^ E := by positivity
  -- the first term is beaten by the divergence of the central index
  have hkey : 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E) * r)
      ≤ C * (ν ^ (P - q.2) * ν * (ν ^ (q.2 - 1) * r ^ E)) := by
    have hterm1 : C * (ν ^ (q.2 - 1) * r ^ (E + 1))
        ≤ 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E) * r) := by
      have hrew : ν ^ (q.2 - 1) * r ^ (E + 1) = (ν ^ (q.2 - 1) * r ^ E) * r := by
        rw [pow_succ]; ring
      rw [hrew]
      have hnn : (0 : ℝ) ≤ (ν ^ (q.2 - 1) * r ^ E) * r := by positivity
      nlinarith [hνbig, hfactorpos, hrpos]
    have hterm2 : C * (ν ^ P * r ^ E)
        ≤ C * (ν ^ (P - q.2) * ν * (ν ^ (q.2 - 1) * r ^ E)) := by
      have hchain : ν ^ P ≤ ν ^ (q.2 - 1) * (ν ^ (P - q.2) * ν) := by
        calc ν ^ P ≤ ν ^ (q.2 - 1) * ν ^ (P + 1 - q.2) := hPle
          _ ≤ ν ^ (q.2 - 1) * (ν ^ (P - q.2) * ν) :=
              mul_le_mul_of_nonneg_left hmle (by positivity)
      have hrE : (0 : ℝ) ≤ r ^ E := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hchain hrE, hC]
    rw [hsplit] at hhalf
    linarith
  -- reading off the bound on the radius
  have hfinal : 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)) * r
      ≤ (4 * C * ν ^ (P - q.2)) * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E))) := by
    calc 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)) * r
        = 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E) * r) := by ring
      _ ≤ C * (ν ^ (P - q.2) * ν * (ν ^ (q.2 - 1) * r ^ E)) := hkey
      _ = (4 * C * ν ^ (P - q.2)) * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E))) := by ring
  have hposfac : (0 : ℝ) < 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)) := by positivity
  have hmul : r * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)))
      ≤ (4 * C * ν ^ (P - q.2)) * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E))) := by
    calc r * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)))
        = 1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E)) * r := by ring
      _ ≤ (4 * C * ν ^ (P - q.2)) * (1 / 4 * (ν * (ν ^ (q.2 - 1) * r ^ E))) := hfinal
  exact le_of_mul_le_mul_right hmul hposfac

/-- **No transcendental entire solution when the dominant monomial is derivative-maximal.**  If the
maximal-weight monomial with the most derivative factors also has no competitor with more derivative
factors, the previous bound reads `r ≤ C`, which fails at large radii. -/
theorem not_transcendental_of_tie_dominant
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {q : ℕ × ℕ} (hq : q ∈ S) (hqd : q.1 + q.2 = d) (hAq : A q ≠ 0)
    (hq1 : 1 ≤ q.2) (hdegq : q.2 ≤ (A q).natDegree)
    (htie : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2) ∨
        ((A p).natDegree + (d - p.2) = (A q).natDegree + (d - q.2) ∧ p.2 + 1 ≤ q.2))
    (hmaxT : ∀ p ∈ S, p.1 + p.2 = d → p ≠ q → p.2 ≤ q.2) : False := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    exists_radius_le_centralIndex_pow ha hn₀ htrans hdeg hrel hq hqd hAq hq1 hdegq htie
      (P := q.2) hmaxT
  obtain ⟨r, hR, _, hb⟩ := hbound (C + 1)
  rw [show q.2 - q.2 = 0 from by omega, pow_zero, mul_one] at hb
  linarith


/-! ## The assembled statement

Nothing above required a choice: the dominant monomial is determined by the equation, first by maximal
Newton weight and then by maximal derivative degree among the monomials attaining it.  Carrying out
that selection turns the two readings into one theorem about the equation alone. -/

/-- **Positive order when some top monomial is coefficient-heavy.**  If a single top-degree monomial
has a nonzero coefficient of degree at least its own derivative degree — for instance the pure
monomial `A_d·f^d` whenever `A_d ≠ 0` — then every transcendental entire solution obeys

`r ≤ C·ν(r)^d`  at arbitrarily large radii,

so its Wiman exponent is at least `1/d`.  The dominant monomial is selected inside the proof: maximal
weight first, then maximal derivative degree among the ties.  One coefficient-heavy monomial pushes
the maximal weight to at least `d`, which is exactly the statement that the dominant monomial is
itself coefficient-heavy.  If it has no derivative factor the weight comparison is automatically
strict, and if it has one the tie reading applies. -/
theorem exists_radius_le_centralIndex_pow_of_top_coefficient_degree
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    (hsome : ∃ p ∈ S, p.1 + p.2 = d ∧ A p ≠ 0 ∧ p.2 ≤ (A p).natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ d := by
  classical
  -- discard the vanishing coefficients
  set S' : Finset (ℕ × ℕ) := S.filter (fun p => A p ≠ 0) with hS'def
  have hS'sub : S' ⊆ S := by rw [hS'def]; exact Finset.filter_subset _ _
  have hmemS' : ∀ p, p ∈ S' ↔ p ∈ S ∧ A p ≠ 0 := by
    intro p
    rw [hS'def, Finset.mem_filter]
  have hdeg' : ∀ p ∈ S', p.1 + p.2 ≤ d := fun p hp => hdeg p (hS'sub hp)
  have hrel' : ∀ w : ℂ,
      ∑ p ∈ S', (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0 := by
    intro w
    rw [Finset.sum_subset hS'sub, hrel w]
    intro x hx hxn
    have hA0 : A x = 0 := by
      by_contra hne
      exact hxn ((hmemS' x).mpr ⟨hx, hne⟩)
    rw [hA0]
    simp
  -- select the dominant monomial
  set Stop : Finset (ℕ × ℕ) := S'.filter (fun p => p.1 + p.2 = d) with hStopdef
  have hmemStop : ∀ p, p ∈ Stop ↔ p ∈ S' ∧ p.1 + p.2 = d := by
    intro p
    rw [hStopdef, Finset.mem_filter]
  obtain ⟨p₀, hp₀S, hp₀d, hp₀A, hp₀deg⟩ := hsome
  have hp₀Stop : p₀ ∈ Stop := (hmemStop p₀).mpr ⟨(hmemS' p₀).mpr ⟨hp₀S, hp₀A⟩, hp₀d⟩
  have hStopne : Stop.Nonempty := ⟨p₀, hp₀Stop⟩
  obtain ⟨q₁, hq₁mem, hq₁max⟩ :=
    Finset.exists_max_image Stop (fun p => (A p).natDegree + (d - p.2)) hStopne
  set W : ℕ := (A q₁).natDegree + (d - q₁.2) with hWdef
  set Tie : Finset (ℕ × ℕ) := Stop.filter (fun p => (A p).natDegree + (d - p.2) = W) with hTiedef
  have hmemTie : ∀ p, p ∈ Tie ↔ p ∈ Stop ∧ (A p).natDegree + (d - p.2) = W := by
    intro p
    rw [hTiedef, Finset.mem_filter]
  have hTiene : Tie.Nonempty := ⟨q₁, (hmemTie q₁).mpr ⟨hq₁mem, by rw [hWdef]⟩⟩
  obtain ⟨q, hqTie, hqmax⟩ := Finset.exists_max_image Tie (fun p => p.2) hTiene
  have hqStop : q ∈ Stop := ((hmemTie q).mp hqTie).1
  have hqW : (A q).natDegree + (d - q.2) = W := ((hmemTie q).mp hqTie).2
  have hqS' : q ∈ S' := ((hmemStop q).mp hqStop).1
  have hqd : q.1 + q.2 = d := ((hmemStop q).mp hqStop).2
  have hAq : A q ≠ 0 := ((hmemS' q).mp hqS').2
  have hq2d : q.2 ≤ d := by have := hdeg' q hqS'; omega
  -- the weight comparison at the selected monomial
  have htie : ∀ p ∈ S', p.1 + p.2 = d → p ≠ q →
      (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2) ∨
        ((A p).natDegree + (d - p.2) = (A q).natDegree + (d - q.2) ∧ p.2 + 1 ≤ q.2) := by
    intro p hpS' hpd hpne
    have hpStop : p ∈ Stop := (hmemStop p).mpr ⟨hpS', hpd⟩
    have hle : (A p).natDegree + (d - p.2) ≤ W := by
      have := hq₁max p hpStop
      rw [hWdef]
      exact this
    rcases lt_or_eq_of_le hle with hlt | heq
    · left
      omega
    · right
      have hpTie : p ∈ Tie := (hmemTie p).mpr ⟨hpStop, heq⟩
      have h2 : p.2 ≤ q.2 := hqmax p hpTie
      have hne2 : p.2 ≠ q.2 := by
        intro h
        exact hpne (Prod.ext (by omega) h)
      exact ⟨by omega, by omega⟩
  -- a coefficient-heavy top monomial forces the maximal weight to be at least `d`
  have hp₀2d : p₀.2 ≤ d := by have := hdeg p₀ hp₀S; omega
  have hWge : d ≤ W := by
    have h1 : (A p₀).natDegree + (d - p₀.2) ≤ W := by
      have := hq₁max p₀ hp₀Stop
      rw [hWdef]
      exact this
    omega
  have hdegq : q.2 ≤ (A q).natDegree := by omega
  have hP : ∀ p ∈ S', p.1 + p.2 = d → p ≠ q → p.2 ≤ d := by
    intro p hpS' _ _
    have := hdeg' p hpS'
    omega
  rcases Nat.eq_zero_or_pos q.2 with hq0 | hq1
  · -- no derivative factor: the weight comparison is strict
    have hweight : ∀ p ∈ S', p.1 + p.2 = d → p ≠ q →
        (A p).natDegree + (d - p.2) + 1 ≤ (A q).natDegree + (d - q.2) := by
      intro p hpS' hpd hpne
      rcases htie p hpS' hpd hpne with h | ⟨_, h2⟩
      · exact h
      · omega
    obtain ⟨C, hC, hbound⟩ :=
      exists_centralIndex_pow_mul_radius_le ha hn₀ htrans hdeg' hrel' hqS' hqd hAq hdegq
        hweight (P := d) hP
    refine ⟨C, hC, ?_⟩
    intro R
    obtain ⟨r, hR, _, _, hb⟩ := hbound R
    refine ⟨r, hR, ?_⟩
    rw [hq0, pow_zero, one_mul] at hb
    exact hb
  · -- a derivative factor: the tie reading applies
    obtain ⟨C, hC, hbound⟩ :=
      exists_radius_le_centralIndex_pow ha hn₀ htrans hdeg' hrel' hqS' hqd hAq hq1 hdegq
        htie (P := d) hP
    refine ⟨C, hC, ?_⟩
    intro R
    obtain ⟨r, hR, hν1, hb⟩ := hbound R
    refine ⟨r, hR, ?_⟩
    have hpow : ((centralIndex a r : ℕ) : ℝ) ^ (d - q.2) ≤ ((centralIndex a r : ℕ) : ℝ) ^ d :=
      pow_le_pow_right₀ hν1 (by omega)
    calc r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ (d - q.2) := hb
      _ ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_left hpow hC.le


/-- **Positive order whenever the pure monomial survives.**  If `A_d·f^d` occurs in the relation with
a nonzero coefficient, every transcendental entire solution has `r ≤ C·ν(r)^d` at arbitrarily large
radii.  The pure monomial has no derivative factor, so it is coefficient-heavy for free. -/
theorem exists_radius_le_centralIndex_pow_of_pure_monomial
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    (hmem : ((d, 0) : ℕ × ℕ) ∈ S) (hA0 : A ((d, 0) : ℕ × ℕ) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ d :=
  exists_radius_le_centralIndex_pow_of_top_coefficient_degree ha hn₀ htrans hdeg hrel
    ⟨((d, 0) : ℕ × ℕ), hmem, by simp, hA0, by simp⟩

/-! ## The linear equation

The hypothesis of the assembled theorem is a condition on a single monomial, and it holds for the
first-order linear homogeneous equation with constant leading coefficient — the family of all
`exp` of a polynomial. -/

/-- **The central index of a solution of `c·f' + B·f = 0` grows at least linearly.**  A transcendental
entire solution of a first-order linear homogeneous equation with constant leading coefficient
satisfies `r ≤ C·ν(r)` at arbitrarily large radii.

The dominant monomial is `f` itself: the derivative monomial has weight `0` and the undifferentiated
one weight `deg B + 1`, so the coefficient-heaviness condition holds vacuously at the dominant
monomial and fails at the other, which therefore cannot be dominant.

The bound is sharp: for `f = exp` the central index is asymptotically `r`. -/
theorem exists_radius_le_centralIndex_of_linear
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {c : ℂ} {B : Polynomial ℂ} (hB : B ≠ 0)
    (hrel : ∀ w : ℂ, c * deriv (coeffFun a) w + B.eval w * coeffFun a w = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      r ≤ C * ((centralIndex a r : ℕ) : ℝ) := by
  classical
  set S : Finset (ℕ × ℕ) := {((0, 1) : ℕ × ℕ), ((1, 0) : ℕ × ℕ)} with hSdef
  set A : ℕ × ℕ → Polynomial ℂ :=
    fun p => if p = ((0, 1) : ℕ × ℕ) then Polynomial.C c else B with hAdef
  have hne : ((0, 1) : ℕ × ℕ) ≠ ((1, 0) : ℕ × ℕ) := by decide
  have hmemS : ∀ p : ℕ × ℕ, p ∈ S ↔ p = ((0, 1) : ℕ × ℕ) ∨ p = ((1, 0) : ℕ × ℕ) := by
    intro p
    rw [hSdef, Finset.mem_insert, Finset.mem_singleton]
  have hA01 : A ((0, 1) : ℕ × ℕ) = Polynomial.C c := by rw [hAdef]; simp
  have hA10 : A ((1, 0) : ℕ × ℕ) = B := by
    rw [hAdef]
    simp [hne.symm]
  have hdeg : ∀ p ∈ S, p.1 + p.2 ≤ 1 := by
    intro p hp
    rcases (hmemS p).mp hp with h | h <;> rw [h] <;> norm_num
  have hrel' : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0 := by
    intro w
    rw [hSdef, Finset.sum_pair hne, hA01, hA10]
    simpa using hrel w
  have hsome : ∃ p ∈ S, p.1 + p.2 = 1 ∧ A p ≠ 0 ∧ p.2 ≤ (A p).natDegree := by
    refine ⟨((1, 0) : ℕ × ℕ), (hmemS _).mpr (Or.inr rfl), by norm_num, ?_, ?_⟩
    · rw [hA10]
      exact hB
    · simp
  obtain ⟨C, hC, hbound⟩ :=
    exists_radius_le_centralIndex_pow_of_top_coefficient_degree ha hn₀ htrans hdeg hrel' hsome
  refine ⟨C, hC, ?_⟩
  intro R
  obtain ⟨r, hR, hb⟩ := hbound R
  refine ⟨r, hR, ?_⟩
  simpa using hb

end GaloisForLFunctions.HTGeometry
