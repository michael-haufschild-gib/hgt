import GaloisForLFunctions.HTGeometry.AutonomousExponentDichotomy
import GaloisForLFunctions.HTGeometry.WimanValironAsymptotic
import GaloisForLFunctions.HTGeometry.CentralIndexDivergence
import GaloisForLFunctions.HTGeometry.GoldbergFiniteOrder

/-!
# The Euler relation forces a polynomial

An entire `f` satisfying an algebraic relation between `f` and the Euler derivative `z f′`,

```text
∑_{k ≤ m} C_k(f(z))·(z f′(z))^k = 0,
```

cannot be transcendental once its central index is known to be polynomially bounded.  At a
Wiman--Valiron radius the Euler quotient `z f′/f` is close to the central index `ν(r)`, so the
exponent dichotomy of the relation reads

```text
ν(r) ≤ 2K      or      c·μ(r) ≤ (3ν(r)/2)^m .
```

For a transcendental function `ν(r) → ∞`, so the first alternative fails at every large radius and
the second bounds the maximum term by a power of `ν(r)`, hence by a power of `r`.  The good radii are
dense in every window and `μ` is monotone, so the power bound holds at *every* large radius — and a
transcendental maximum term outgrows every power.

The Euler form is what appears after substituting `z = e^t` in an autonomous first-order equation:
`F(t) = f(e^t)` satisfies `F′ = c(F)` exactly when `f` satisfies the relation above.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set

variable {a : ℕ → ℂ}

set_option maxHeartbeats 2000000 in
/-- **A transcendental entire function cannot satisfy an Euler relation with polynomially bounded
central index.**  The Wiman--Valiron quotient turns the exponent dichotomy into a dichotomy for the
central index; divergence of the central index kills the tame alternative, and the wild alternative
bounds the maximum term by a power of the radius. -/
theorem false_of_euler_relation_of_centralIndex_le_pow
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1),
      (C k).eval (coeffFun a z) * (z * deriv (coeffFun a) z) ^ k = 0)
    {Cg : ℝ} {Kg : ℕ} (hCg : 0 < Cg)
    (hgold : ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ Cg * t ^ Kg) :
    False := by
  classical
  obtain ⟨K, c, R₀, hK1, hc0, hc1, hR₀1, hdich⟩ :=
    exists_dichotomy_of_relation (Y := coeffFun a) (W := fun z => z * deriv (coeffFun a) z)
      hm hCm hrel
  obtain ⟨R₁, hWV⟩ := exists_radius_point_logDeriv_close_centralIndex_window ha hn₀ htrans
    (eps := 1 / 2) (by norm_num)
  set W' : ℝ := Nevanlinna.borelWindow ((1 : ℝ) / 4) + 1 with hW'
  have hW'0 : 0 ≤ W' := by
    have := Nevanlinna.one_le_borelWindow ((1 : ℝ) / 4)
    rw [hW']
    linarith
  -- thresholds
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hgold
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    ((tendsto_centralIndex_atTop ha htrans).eventually_ge_atTop N)
  obtain ⟨n₁, hn₁ge, hn₁ne⟩ := htrans 1
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp
    ((tendsto_maxTerm_atTop ha hn₁ne (by omega)).eventually_ge_atTop R₀)
  set T : ℝ := max 1 (max T₁ (max T₂ T₃)) with hT
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT0 : (0 : ℝ) < T := by linarith
  set X₀ : ℝ := max R₁ (Real.log T) with hX₀
  set B : ℝ := (3 * Cg * (Real.exp W') ^ Kg / 2) ^ m / c with hB
  have hB0 : 0 < B := by
    rw [hB]
    have : (0 : ℝ) < 3 * Cg * (Real.exp W') ^ Kg / 2 := by positivity
    positivity
  -- the power bound at every large radius
  have hmain : ∀ x : ℝ, X₀ ≤ x → maxTerm a (Real.exp x) ≤ B * (Real.exp x) ^ (Kg * m) := by
    intro x hx
    have hxR₁ : R₁ ≤ x := le_trans (le_max_left _ _) hx
    have hxT : Real.log T ≤ x := le_trans (le_max_right _ _) hx
    have hTexp : T ≤ Real.exp x := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr hxT
    obtain ⟨x', hx'mem, z, hznorm, hmaxle, hclose⟩ := hWV x hxR₁
    have hx'1 : x ≤ x' := hx'mem.1
    have hx'2 : x' ≤ x + W' := by
      have := hx'mem.2
      rw [hW']
      linarith [this]
    set r' : ℝ := Real.exp x' with hr'
    have hr'0 : 0 < r' := Real.exp_pos _
    have hr'ge : Real.exp x ≤ r' := Real.exp_le_exp.mpr hx'1
    have hr'T : T ≤ r' := le_trans hTexp hr'ge
    have hT1le : T₁ ≤ r' := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right (1 : ℝ) _) le_rfl)) hr'T
    have hT2le : T₂ ≤ r' := by
      refine le_trans ?_ hr'T
      rw [hT]
      exact le_trans (le_trans (le_max_left T₂ T₃) (le_max_right T₁ _)) (le_max_right 1 _)
    have hT3le : T₃ ≤ r' := by
      refine le_trans ?_ hr'T
      rw [hT]
      exact le_trans (le_trans (le_max_right T₂ T₃) (le_max_right T₁ _)) (le_max_right 1 _)
    set nu : ℝ := ((centralIndex a r' : ℕ) : ℝ) with hnu
    have hnu0 : 0 ≤ nu := by positivity
    have hnugold : nu ≤ Cg * r' ^ Kg := hT₁ r' hT1le
    have hnubig : 2 * K < nu := by
      have := hT₂ r' hT2le
      have hcast : (N : ℝ) ≤ nu := by
        rw [hnu]
        exact_mod_cast this
      linarith [hN, hcast]
    have hmaxR₀ : R₀ ≤ maxTerm a r' := hT₃ r' hT3le
    have hFznorm : R₀ ≤ ‖coeffFun a z‖ := le_trans hmaxR₀ hmaxle
    have hFz0 : coeffFun a z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hFznorm
      linarith
    have hFzpos : (0 : ℝ) < ‖coeffFun a z‖ := by linarith
    set Q : ℂ := z * deriv (coeffFun a) z / coeffFun a z with hQ
    have hQeq : z * deriv (coeffFun a) z = Q * coeffFun a z := by
      rw [hQ, div_mul_cancel₀ _ hFz0]
    have hnormcast : ‖((centralIndex a r' : ℕ) : ℂ)‖ = nu := by
      rw [hnu]
      simp
    have hQhigh : ‖Q‖ ≤ 3 * nu / 2 := by
      have h1 : ‖Q‖ ≤ ‖Q - ((centralIndex a r' : ℕ) : ℂ)‖ + ‖((centralIndex a r' : ℕ) : ℂ)‖ :=
        norm_le_norm_sub_add _ _
      rw [hnormcast] at h1
      have h2 := hclose
      linarith [h1, h2]
    have hQlow : nu / 2 ≤ ‖Q‖ := by
      have h1 : ‖((centralIndex a r' : ℕ) : ℂ)‖ - ‖Q‖ ≤ ‖((centralIndex a r' : ℕ) : ℂ) - Q‖ :=
        norm_sub_norm_le _ _
      rw [hnormcast, norm_sub_rev] at h1
      have h2 := hclose
      linarith [h1, h2]
    have hWnorm : ‖z * deriv (coeffFun a) z‖ = ‖Q‖ * ‖coeffFun a z‖ := by
      rw [hQeq, norm_mul]
    -- the dichotomy at `z`
    have hwild : c * maxTerm a r' ≤ (3 * nu / 2) ^ m := by
      rcases hdich z hFznorm with htame | hwild
      · exfalso
        rw [hWnorm] at htame
        have hQK : ‖Q‖ ≤ K := by
          by_contra hcon
          push Not at hcon
          nlinarith [htame, hFzpos, hcon]
        linarith [hQlow, hQK, hnubig]
      · have hstep : c * ‖coeffFun a z‖ ^ (m + 1) ≤ (‖Q‖ * ‖coeffFun a z‖) ^ m := by
          rw [← hWnorm]
          exact hwild
        have hpow : (‖Q‖ * ‖coeffFun a z‖) ^ m ≤ (3 * nu / 2) ^ m * ‖coeffFun a z‖ ^ m := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hQhigh m)
            (by positivity)
        have hFm : (0 : ℝ) < ‖coeffFun a z‖ ^ m := by positivity
        have hsplit : c * ‖coeffFun a z‖ ^ (m + 1)
            = (c * ‖coeffFun a z‖) * ‖coeffFun a z‖ ^ m := by ring
        rw [hsplit] at hstep
        have hcancel : c * ‖coeffFun a z‖ ≤ (3 * nu / 2) ^ m := by
          by_contra hcon
          push Not at hcon
          nlinarith [hstep, hpow, hFm, hcon]
        have hmt : c * maxTerm a r' ≤ c * ‖coeffFun a z‖ :=
          mul_le_mul_of_nonneg_left hmaxle hc0.le
        linarith [hmt, hcancel]
    -- convert the central-index bound into a power of `exp x`
    have hr'pow : r' ^ Kg ≤ (Real.exp x) ^ Kg * (Real.exp W') ^ Kg := by
      have h1 : r' ≤ Real.exp x * Real.exp W' := by
        rw [hr', ← Real.exp_add]
        exact Real.exp_le_exp.mpr hx'2
      calc r' ^ Kg ≤ (Real.exp x * Real.exp W') ^ Kg :=
            pow_le_pow_left₀ hr'0.le h1 Kg
        _ = (Real.exp x) ^ Kg * (Real.exp W') ^ Kg := by rw [mul_pow]
    have hnupow : 3 * nu / 2 ≤ 3 * Cg * (Real.exp W') ^ Kg / 2 * (Real.exp x) ^ Kg := by
      have h1 : nu ≤ Cg * ((Real.exp x) ^ Kg * (Real.exp W') ^ Kg) := by
        refine le_trans hnugold ?_
        exact mul_le_mul_of_nonneg_left hr'pow hCg.le
      nlinarith [h1]
    have hnn : (0 : ℝ) ≤ 3 * nu / 2 := by linarith
    have hfin : (3 * nu / 2) ^ m
        ≤ (3 * Cg * (Real.exp W') ^ Kg / 2) ^ m * ((Real.exp x) ^ Kg) ^ m := by
      calc (3 * nu / 2) ^ m
          ≤ (3 * Cg * (Real.exp W') ^ Kg / 2 * (Real.exp x) ^ Kg) ^ m :=
            pow_le_pow_left₀ hnn hnupow m
        _ = (3 * Cg * (Real.exp W') ^ Kg / 2) ^ m * ((Real.exp x) ^ Kg) ^ m := by rw [mul_pow]
    have hmono : maxTerm a (Real.exp x) ≤ maxTerm a r' :=
      maxTerm_mono ha (Real.exp_pos x) hr'ge
    have hcm : c * maxTerm a (Real.exp x)
        ≤ (3 * Cg * (Real.exp W') ^ Kg / 2) ^ m * (Real.exp x) ^ (Kg * m) := by
      have hpm : ((Real.exp x) ^ Kg) ^ m = (Real.exp x) ^ (Kg * m) := by
        rw [← pow_mul]
      rw [← hpm]
      have h1 : c * maxTerm a (Real.exp x) ≤ c * maxTerm a r' :=
        mul_le_mul_of_nonneg_left hmono hc0.le
      linarith [h1, hwild, hfin]
    rw [hB, div_mul_eq_mul_div, le_div_iff₀ hc0]
    linarith [hcm]
  -- a transcendental maximum term outgrows every power
  have hdiv := (tendsto_maxTerm_div_pow_atTop ha htrans (Kg * m)).eventually_gt_atTop B
  obtain ⟨T₄, hT₄⟩ := eventually_atTop.mp hdiv
  set x₄ : ℝ := max X₀ (Real.log (max T₄ 1)) with hx₄
  have hx₄X : X₀ ≤ x₄ := le_max_left _ _
  have hmaxT₄ : (1 : ℝ) ≤ max T₄ 1 := le_max_right _ _
  have hexp₄ : max T₄ 1 ≤ Real.exp x₄ := by
    calc max T₄ 1 = Real.exp (Real.log (max T₄ 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp x₄ := Real.exp_le_exp.mpr (le_max_right _ _)
  have hT₄le : T₄ ≤ Real.exp x₄ := le_trans (le_max_left _ _) hexp₄
  have hbig := hT₄ (Real.exp x₄) hT₄le
  have hbd := hmain x₄ hx₄X
  have hpow0 : (0 : ℝ) < (Real.exp x₄) ^ (Kg * m) := by positivity
  rw [lt_div_iff₀ hpow0] at hbig
  linarith [hbd, hbig]

set_option maxHeartbeats 2000000 in
/-- **The Euler relation forces a polynomial.**  An entire `f` satisfying
`∑_{k ≤ m} C_k(f)·(z f′)^k = 0` has only finitely many nonzero Taylor coefficients, provided some
index `ms ≥ 1` carries the maximal total degree `deg C_k + k` and is the largest such index.
Gol'dberg's bound then makes the central index polynomial in the radius, and the exponent dichotomy
at the Wiman--Valiron radii bounds the maximum term by a power of the radius, which a transcendental
function cannot obey. -/
theorem eventually_taylorCoeff_eq_zero_of_euler_relation
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ} (hCm : C m ≠ 0)
    {ms : ℕ} (hms1 : 1 ≤ ms) (hmsm : ms ≤ m) (hCms : C ms ≠ 0)
    (hdegtop : ∀ k ≤ m, (C k).natDegree + k ≤ (C ms).natDegree + ms)
    (htopmax : ∀ k ≤ m, (C k).natDegree + k = (C ms).natDegree + ms → k ≤ ms)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (f z) * (z * deriv f z) ^ k = 0) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → taylorCoeff f n = 0 := by
  classical
  set a : ℕ → ℂ := taylorCoeff f with hadef
  by_cases htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0
  swap
  · push Not at htrans
    obtain ⟨M, hM⟩ := htrans
    exact ⟨M, hM⟩
  exfalso
  have ha : EntireCoeffs a := entireCoeffs_taylorCoeff hf
  have hfeq : coeffFun a = f := coeffFun_taylorCoeff hf
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  set D : ℕ := (C ms).natDegree with hD
  set d : ℕ := D + ms with hd
  set S : Finset (ℕ × ℕ) :=
    Finset.filter (fun p => (C p.2).coeff p.1 ≠ 0)
      ((Finset.range (d + 1)) ×ˢ (Finset.range (m + 1))) with hS
  set A : ℕ × ℕ → Polynomial ℂ :=
    fun p => Polynomial.C ((C p.2).coeff p.1) * Polynomial.X ^ p.2 with hA
  have hAeval : ∀ (p : ℕ × ℕ) (z : ℂ), (A p).eval z = (C p.2).coeff p.1 * z ^ p.2 := by
    intro p z
    rw [hA]
    simp
  have hcoeffle : ∀ (k j : ℕ), (C k).coeff j ≠ 0 → j ≤ (C k).natDegree := by
    intro k j hj
    by_contra hcon
    exact hj (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hdegbound : ∀ k ≤ m, ∀ j, (C k).coeff j ≠ 0 → j + k ≤ d := by
    intro k hk j hj
    have hjle := hcoeffle k j hj
    have := hdegtop k hk
    omega
  have hrel' : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0 := by
    intro w
    rw [hfeq]
    have hfull : ∑ p ∈ (Finset.range (d + 1)) ×ˢ (Finset.range (m + 1)),
        (A p).eval w * (f w) ^ p.1 * (deriv f w) ^ p.2
        = ∑ p ∈ S, (A p).eval w * (f w) ^ p.1 * (deriv f w) ^ p.2 := by
      rw [hS]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro p _ hne hzero
      apply hne
      rw [hAeval p w, hzero, zero_mul, zero_mul, zero_mul]
    rw [← hfull, Finset.sum_product]
    have hswap : ∑ j ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (m + 1),
        (A (j, k)).eval w * (f w) ^ (j, k).1 * (deriv f w) ^ (j, k).2
        = ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (d + 1),
          (C k).coeff j * (f w) ^ j * (w * deriv f w) ^ k := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAeval (j, k) w, mul_pow]
      ring
    rw [hswap]
    rw [← hrel w]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdk : (C k).natDegree < d + 1 := by
      have := hdegtop k hkm
      omega
    rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range' hdk]
  have hmem : (d - ms, ms) ∈ S := by
    rw [hS]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · show (C ms).coeff (d - ms) ≠ 0
      have hdm : d - ms = (C ms).natDegree := by omega
      rw [hdm]
      exact Polynomial.leadingCoeff_ne_zero.mpr hCms
  have hAne : A (d - ms, ms) ≠ 0 := by
    rw [hA]
    have hdm : d - ms = (C ms).natDegree := by omega
    simp only [hdm]
    refine mul_ne_zero ?_ (pow_ne_zero ms Polynomial.X_ne_zero)
    exact Polynomial.C_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hCms)
  obtain ⟨Cg, Kg, hCg, hgold⟩ :=
    exists_centralIndex_le_pow_of_relation ha hn₀ htrans
      (S := S) (A := A) (d := d) (m := ms)
      (fun p hp => by
        rw [hS] at hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hk⟩ := Finset.mem_product.mp hp1
        exact hdegbound p.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) p.1 hp2)
      hrel' hms1 (by omega) hmem
      (fun p hp htot => by
        rw [hS] at hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hk⟩ := Finset.mem_product.mp hp1
        have hkm : p.2 ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hjle := hcoeffle p.2 p.1 hp2
        have hle := hdegtop p.2 hkm
        refine htopmax p.2 hkm ?_
        omega)
      hAne
  refine false_of_euler_relation_of_centralIndex_le_pow ha hn₀ htrans hm hCm ?_ hCg hgold
  intro z
  rw [hfeq]
  exact hrel z

end GaloisForLFunctions.HTGeometry
