import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceSymmetricZeroFreeCusp

/-!
# Actual Xi dyadic roots on a symmetric classical zero-free cusp

The Euler chamber has analytic `2^k`-th roots of the completed Riemann `xi` at every level.
The classical de la Vallee Poussin zero-free region lets each chosen Euler root continue across
both high cusps.  Root-of-unity normalization at one point makes each cusp branch agree with the
chosen Euler germ; connected-overlap uniqueness and two-chart gluing then produce one root on the
whole conjugation-symmetric union.

This is an unconditional all-level root producer for actual `xi` on one open preconnected region
strictly larger than `farHalf`.  The cusp boundary still retreats to `Re s = 1`, so this result does
not construct the roots on `rightHalf` required for RH.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- The Euler chamber and the two classical cusps form one open region. -/
theorem isOpen_firstTraceSymmetricZeroFreeCusp {T : ℝ} (hT : 4 ≤ T) :
    IsOpen (firstTraceSymmetricZeroFreeCusp T) := by
  simpa [firstTraceSymmetricZeroFreeCusp] using
    ((isOpen_firstTraceZeroFreeCusp hT).union isOpen_farHalf).union
      (isOpen_firstTraceZeroFreeLowerCusp hT)

/-- The common Euler chamber connects the upper and lower classical cusps. -/
theorem isPreconnected_firstTraceSymmetricZeroFreeCusp {T : ℝ} (hT : 4 ≤ T) :
    IsPreconnected (firstTraceSymmetricZeroFreeCusp T) := by
  let aU : ℂ := 2 + ((T + 1 : ℝ) : ℂ) * I
  have haU : aU ∈ firstTraceZeroFreeCusp T := by
    have him : T < aU.im := by norm_num [aU]
    have hmax : max T aU.im = aU.im := max_eq_right (le_of_lt him)
    have hlogpos : 0 < Real.log aU.im := Real.log_pos (by norm_num [aU]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T aU.im < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log aU.im := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨him, hedge.trans (by norm_num [aU])⟩
  have haUFar : aU ∈ farHalf := by rw [mem_farHalf]; norm_num [aU]
  have hUF : IsPreconnected (firstTraceZeroFreeCusp T ∪ farHalf) :=
    IsPreconnected.union aU haU haUFar
      (isSimplyConnected_firstTraceZeroFreeCusp hT).isPathConnected.isConnected.isPreconnected
      convex_farHalf.isPreconnected
  let aL : ℂ := 2 - ((T + 1 : ℝ) : ℂ) * I
  have haL : aL ∈ firstTraceZeroFreeLowerCusp T := by
    rw [firstTraceZeroFreeLowerCusp_eq]
    have him : aL.im < -T := by norm_num [aL]
    have hmax : max T (-aL.im) = -aL.im := max_eq_right (by linarith [him])
    have hlogpos : 0 < Real.log (-aL.im) := Real.log_pos (by norm_num [aL]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T (-aL.im) < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log (-aL.im) := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨him, hedge.trans (by norm_num [aL])⟩
  have haLFar : aL ∈ farHalf := by rw [mem_farHalf]; norm_num [aL]
  rw [firstTraceSymmetricZeroFreeCusp]
  exact IsPreconnected.union aL (Or.inr haLFar) haL hUF
    (isSimplyConnected_firstTraceZeroFreeLowerCusp hT).isPathConnected.isConnected.isPreconnected

/-- Xi is nonzero on the upper classical cusp supplied by an explicit zero-free region. -/
theorem xi_ne_zero_on_firstTraceZeroFreeCusp_of_zeroFree
    {T₀ T : ℝ} (hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) {s : ℂ}
    (hs : s ∈ firstTraceZeroFreeCusp T) :
    xi s ≠ 0 := by
  have hsright := firstTraceZeroFreeCusp_subset_rightHalf hT hs
  have hfirst := poleClearedFirstTraceExponentialContinuation_ne_zero_on_cusp
    hT₀ hzf hT₀T hT hs
  have hfirstAn :=
    analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf s hsright
  have hfirstOrder :
      analyticOrderAt poleClearedFirstTraceExponentialContinuation s = 0 :=
    hfirstAn.analyticOrderAt_eq_zero.mpr hfirst
  have hxiOrder : analyticOrderAt xi s = 0 := by
    rw [← analyticOrderAt_poleClearedFirstTraceExponentialContinuation_eq_xi hsright]
    exact hfirstOrder
  exact (xi_analyticOnNhd rightHalf s hsright).analyticOrderAt_eq_zero.mp hxiOrder

/-- Xi is nonzero on the lower reflected cusp supplied by an explicit zero-free region. -/
theorem xi_ne_zero_on_firstTraceZeroFreeLowerCusp_of_zeroFree
    {T₀ T : ℝ} (hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) {s : ℂ}
    (hs : s ∈ firstTraceZeroFreeLowerCusp T) :
    xi s ≠ 0 := by
  have hsright := firstTraceZeroFreeLowerCusp_subset_rightHalf hT hs
  have hfirst := poleClearedFirstTraceExponentialContinuation_ne_zero_on_lowerCusp
    hT₀ hzf hT₀T hT hs
  have hfirstAn :=
    analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf s hsright
  have hfirstOrder :
      analyticOrderAt poleClearedFirstTraceExponentialContinuation s = 0 :=
    hfirstAn.analyticOrderAt_eq_zero.mpr hfirst
  have hxiOrder : analyticOrderAt xi s = 0 := by
    rw [← analyticOrderAt_poleClearedFirstTraceExponentialContinuation_eq_xi hsright]
    exact hfirstOrder
  exact (xi_analyticOnNhd rightHalf s hsright).analyticOrderAt_eq_zero.mp hxiOrder

/-- A chosen Euler-side dyadic Xi root extends to the upper classical cusp. -/
theorem exists_xi_firstTraceZeroFreeCusp_extension_of_farHalf_root
    {T₀ T : ℝ} (hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) (k : ℕ)
    (g₁ : ℂ → ℂ) (hg₁ : AnalyticOnNhd ℂ g₁ farHalf)
    (hg₁pow : ∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (firstTraceZeroFreeCusp T) ∧
        (∀ s ∈ firstTraceZeroFreeCusp T, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ (firstTraceZeroFreeCusp T ∩ farHalf) := by
  have hcuspOpen := isOpen_firstTraceZeroFreeCusp hT
  have hcuspSimply := isSimplyConnected_firstTraceZeroFreeCusp hT
  have hcuspRight := firstTraceZeroFreeCusp_subset_rightHalf hT
  obtain ⟨g, hg, hgpow⟩ := Bottcher.exists_analyticOnNhd_pow_eq
    hcuspSimply hcuspOpen ((xi_analyticOnNhd rightHalf).mono hcuspRight)
    (fun s hs => xi_ne_zero_on_firstTraceZeroFreeCusp_of_zeroFree
      hT₀ hzf hT₀T hT hs) Nat.one_le_two_pow
  let a : ℂ := 2 + ((T + 1 : ℝ) : ℂ) * I
  have haCusp : a ∈ firstTraceZeroFreeCusp T := by
    have him : T < a.im := by norm_num [a]
    have hmax : max T a.im = a.im := max_eq_right (le_of_lt him)
    have hlogpos : 0 < Real.log a.im := Real.log_pos (by norm_num [a]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T a.im < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log a.im := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨him, hedge.trans (by norm_num [a])⟩
  have haFar : a ∈ farHalf := by rw [mem_farHalf]; norm_num [a]
  have hxia : xi a ≠ 0 := xi_ne_zero_of_one_lt_re (mem_farHalf.mp haFar)
  have hga : g a ≠ 0 := by
    intro hzero
    have hpow := hgpow a haCusp
    rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
    exact hxia hpow.symm
  let omega : ℂ := g₁ a / g a
  have homegaPow : omega ^ 2 ^ k = 1 := by
    change (g₁ a / g a) ^ 2 ^ k = 1
    rw [div_pow, hg₁pow a haFar, hgpow a haCusp, div_self hxia]
  have hroot : ∀ s ∈ firstTraceZeroFreeCusp T,
      (omega * g s) ^ 2 ^ k = xi s := by
    intro s hs
    rw [mul_pow, homegaPow, one_mul, hgpow s hs]
  have hmatch : omega * g a = g₁ a := by
    change (g₁ a / g a) * g a = g₁ a
    rw [div_mul_cancel₀ _ hga]
  have hscaledAn : AnalyticOnNhd ℂ (fun s => omega * g s)
      (firstTraceZeroFreeCusp T) := fun s hs => analyticAt_const.mul (hg s hs)
  refine ⟨fun s => omega * g s, hscaledAn, hroot, ?_⟩
  exact Bottcher.eqOn_of_pow_eq_of_isPreconnected Nat.one_le_two_pow
    (convex_firstTraceZeroFreeCusp_inter_farHalf hT).isPreconnected
    (hscaledAn.continuousOn.mono inter_subset_left)
    (hg₁.continuousOn.mono inter_subset_right)
    (fun s hs => by
      intro hzero
      have hpow := hg₁pow s hs.2
      rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
      exact (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hs.2)) hpow.symm)
    (fun s hs => by rw [hroot s hs.1, hg₁pow s hs.2])
    ⟨haCusp, haFar⟩ hmatch

/-- A chosen Euler-side dyadic Xi root extends to the lower reflected cusp. -/
theorem exists_xi_firstTraceZeroFreeLowerCusp_extension_of_farHalf_root
    {T₀ T : ℝ} (hT₀ : 3 ≤ T₀)
    (hzf : ∀ β γ : ℝ, T₀ ≤ |γ| → β ≤ 1 →
      1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0)
    (hT₀T : T₀ ≤ T) (hT : 4 ≤ T) (k : ℕ)
    (g₁ : ℂ → ℂ) (hg₁ : AnalyticOnNhd ℂ g₁ farHalf)
    (hg₁pow : ∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (firstTraceZeroFreeLowerCusp T) ∧
        (∀ s ∈ firstTraceZeroFreeLowerCusp T, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ (firstTraceZeroFreeLowerCusp T ∩ farHalf) := by
  have hcuspOpen := isOpen_firstTraceZeroFreeLowerCusp hT
  have hcuspSimply := isSimplyConnected_firstTraceZeroFreeLowerCusp hT
  have hcuspRight := firstTraceZeroFreeLowerCusp_subset_rightHalf hT
  obtain ⟨g, hg, hgpow⟩ := Bottcher.exists_analyticOnNhd_pow_eq
    hcuspSimply hcuspOpen ((xi_analyticOnNhd rightHalf).mono hcuspRight)
    (fun s hs => xi_ne_zero_on_firstTraceZeroFreeLowerCusp_of_zeroFree
      hT₀ hzf hT₀T hT hs) Nat.one_le_two_pow
  let a : ℂ := 2 - ((T + 1 : ℝ) : ℂ) * I
  have haCusp : a ∈ firstTraceZeroFreeLowerCusp T := by
    rw [firstTraceZeroFreeLowerCusp_eq]
    have him : a.im < -T := by norm_num [a]
    have hmax : max T (-a.im) = -a.im := max_eq_right (by linarith [him])
    have hlogpos : 0 < Real.log (-a.im) := Real.log_pos (by norm_num [a]; linarith)
    have hedge : firstTraceZeroFreeCuspBoundary T (-a.im) < 1 := by
      dsimp [firstTraceZeroFreeCuspBoundary]
      rw [hmax]
      have : 0 < (1 / 10000 : ℝ) / Real.log (-a.im) := div_pos (by norm_num) hlogpos
      linarith
    exact ⟨him, hedge.trans (by norm_num [a])⟩
  have haFar : a ∈ farHalf := by rw [mem_farHalf]; norm_num [a]
  have hxia : xi a ≠ 0 := xi_ne_zero_of_one_lt_re (mem_farHalf.mp haFar)
  have hga : g a ≠ 0 := by
    intro hzero
    have hpow := hgpow a haCusp
    rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
    exact hxia hpow.symm
  let omega : ℂ := g₁ a / g a
  have homegaPow : omega ^ 2 ^ k = 1 := by
    change (g₁ a / g a) ^ 2 ^ k = 1
    rw [div_pow, hg₁pow a haFar, hgpow a haCusp, div_self hxia]
  have hroot : ∀ s ∈ firstTraceZeroFreeLowerCusp T,
      (omega * g s) ^ 2 ^ k = xi s := by
    intro s hs
    rw [mul_pow, homegaPow, one_mul, hgpow s hs]
  have hmatch : omega * g a = g₁ a := by
    change (g₁ a / g a) * g a = g₁ a
    rw [div_mul_cancel₀ _ hga]
  have hscaledAn : AnalyticOnNhd ℂ (fun s => omega * g s)
      (firstTraceZeroFreeLowerCusp T) := fun s hs => analyticAt_const.mul (hg s hs)
  refine ⟨fun s => omega * g s, hscaledAn, hroot, ?_⟩
  exact Bottcher.eqOn_of_pow_eq_of_isPreconnected Nat.one_le_two_pow
    (convex_firstTraceZeroFreeLowerCusp_inter_farHalf hT).isPreconnected
    (hscaledAn.continuousOn.mono inter_subset_left)
    (hg₁.continuousOn.mono inter_subset_right)
    (fun s hs => by
      intro hzero
      have hpow := hg₁pow s hs.2
      rw [hzero, zero_pow (pow_ne_zero k two_ne_zero)] at hpow
      exact (xi_ne_zero_of_one_lt_re (mem_farHalf.mp hs.2)) hpow.symm)
    (fun s hs => by rw [hroot s hs.1, hg₁pow s hs.2])
    ⟨haCusp, haFar⟩ hmatch

/-- Every Euler-side dyadic Xi root extends across both classical zero-free cusps. -/
theorem exists_xi_symmetricZeroFreeCusp_extension_of_farHalf_root_all_levels :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ (k : ℕ) (g₁ : ℂ → ℂ),
      AnalyticOnNhd ℂ g₁ farHalf →
      (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) →
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g (firstTraceSymmetricZeroFreeCusp T) ∧
          (∀ s ∈ firstTraceSymmetricZeroFreeCusp T, g s ^ 2 ^ k = xi s) ∧
          EqOn g g₁ farHalf := by
  obtain ⟨T₀, hT₀, hzf⟩ := Sieve.exists_zero_free_region_explicit
  let T : ℝ := max T₀ 4
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hT : 4 ≤ T := le_max_right _ _
  refine ⟨T, hT, fun k g₁ hg₁ hg₁pow => ?_⟩
  obtain ⟨gU, hgU, hgUpow, hgUFar⟩ :=
    exists_xi_firstTraceZeroFreeCusp_extension_of_farHalf_root
      hT₀ hzf hT₀T hT k g₁ hg₁ hg₁pow
  obtain ⟨gL, hgL, hgLpow, hgLFar⟩ :=
    exists_xi_firstTraceZeroFreeLowerCusp_extension_of_farHalf_root
      hT₀ hzf hT₀T hT k g₁ hg₁ hg₁pow
  obtain ⟨gUF, hgUF, hgUFUpper, hgUFFar⟩ := Bottcher.analyticOnNhd_glue_twoChart
    (isOpen_firstTraceZeroFreeCusp hT) isOpen_farHalf hgU hg₁ hgUFar
  have hUFLAgree : EqOn gUF gL
      ((firstTraceZeroFreeCusp T ∪ farHalf) ∩ firstTraceZeroFreeLowerCusp T) := by
    intro s hs
    have hnotUpper : s ∉ firstTraceZeroFreeCusp T := by
      intro hu
      exact Set.disjoint_left.mp
        (firstTraceZeroFreeCusp_disjoint_lowerCusp (by linarith [hT])) hu hs.2
    have hfar : s ∈ farHalf := hs.1.resolve_left hnotUpper
    rw [hgUFFar hfar]
    exact (hgLFar ⟨hs.2, hfar⟩).symm
  obtain ⟨g, hg, hgUFg, hgLg⟩ := Bottcher.analyticOnNhd_glue_twoChart
    ((isOpen_firstTraceZeroFreeCusp hT).union isOpen_farHalf)
    (isOpen_firstTraceZeroFreeLowerCusp hT) hgUF hgL hUFLAgree
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [firstTraceSymmetricZeroFreeCusp] using hg
  · intro s hs
    rw [firstTraceSymmetricZeroFreeCusp] at hs
    rcases hs with hsUF | hsL
    · rw [hgUFg hsUF]
      rcases hsUF with hsU | hsFar
      · rw [hgUFUpper hsU]
        exact hgUpow s hsU
      · rw [hgUFFar hsFar]
        exact hg₁pow s hsFar
    · rw [hgLg hsL]
      exact hgLpow s hsL
  · intro s hs
    have hsUF : s ∈ firstTraceZeroFreeCusp T ∪ farHalf := Or.inr hs
    rw [hgUFg hsUF, hgUFFar hs]

/-- Unconditional all-level dyadic roots of actual Xi on one connected symmetric classical cusp. -/
theorem exists_xi_symmetricZeroFreeCusp_arithmetic_extensions_all_levels :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ k : ℕ, ∃ g₁ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g₁ farHalf ∧
        (∀ s ∈ farHalf, g₁ s ^ 2 ^ k = xi s) ∧
        AnalyticOnNhd ℂ g (firstTraceSymmetricZeroFreeCusp T) ∧
        (∀ s ∈ firstTraceSymmetricZeroFreeCusp T, g s ^ 2 ^ k = xi s) ∧
        EqOn g g₁ farHalf := by
  obtain ⟨T, hT, hext⟩ :=
    exists_xi_symmetricZeroFreeCusp_extension_of_farHalf_root_all_levels
  refine ⟨T, hT, fun k => ?_⟩
  obtain ⟨g₁, hg₁, hg₁pow⟩ := exists_farHalf_root k
  obtain ⟨g, hg, hgpow, heq⟩ := hext k g₁ hg₁ hg₁pow
  exact ⟨g₁, g, hg₁, hg₁pow, hg, hgpow, heq⟩

end

end RHTower
