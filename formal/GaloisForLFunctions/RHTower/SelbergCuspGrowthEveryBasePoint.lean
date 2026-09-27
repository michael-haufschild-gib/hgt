import GaloisForLFunctions.RHTower.SelbergGeneralSineRecurrence
import GaloisForLFunctions.HTGeometry.ShiftSpectrumFirstIndex

/-!
# The cusp growth law at every base point

For every member `F` of the extended Selberg class with positive presentation degree `d` and every
base point `s₀ ∈ ℂ`,

```text
limsup_k (‖F(s₀ - k/d)‖/k!)^{1/k} = 1 / (2π · dist(0, Spec F)),   dist(0, Spec F) = d (m₀/q)^{1/d},
```

where `m₀` is the first index with `a_F(m₀) ≠ 0` (`ExtendedSelbergClass.cuspGrowthLaw`).  There is no
exceptional set of base points:

* the asymmetric functional equation holds pointwise at every point far enough to the left
  (`ExtendedSelbergClass.value_eq_asymmetric_of_farLeft`), by continuity from the nonreal
  points above it, where all Gamma arguments are off their poles;
* the sine factor cannot vanish at `2r + 1` consecutive lattice points, because the zeros of the
  `j`-th factor along the lattice are spaced by `d/λ_j` and the rates `λ_j/d` sum to `1/2`
  (`SelbergGammaData.exists_asymmetricS_shift_ne_zero`); simultaneous recurrence from such a point
  bounds the sine factor below frequently;
* the reflected Dirichlet series normalized by `m₀^w` tends to `a_F(m₀)`, so its root tends to
  `m₀^{-1/d}` (`ExtendedSelbergClass.tendsto_norm_reflection_shift_rpow_inv`).

For the full Selberg class `a_F(1) = 1`, so `m₀ = 1` and the constant is `q^{1/d}/(2πd)`
(`SelbergClass.cuspGrowthLaw`).
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The first non-vanishing coefficient -/

theorem ExtendedSelbergClass.exists_coeff_ne_zero (F : ExtendedSelbergClass) :
    ∃ n : ℕ, (F.coeff n : ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  exact F.coeff_ne_zero (ArithmeticFunction.ext fun n => by simpa using h n)

/-- The first index carrying a nonzero coefficient. -/
def ExtendedSelbergClass.firstIndex (F : ExtendedSelbergClass) : ℕ :=
  Nat.find F.exists_coeff_ne_zero

theorem ExtendedSelbergClass.coeff_firstIndex_ne_zero (F : ExtendedSelbergClass) :
    (F.coeff F.firstIndex : ℂ) ≠ 0 :=
  Nat.find_spec F.exists_coeff_ne_zero

theorem ExtendedSelbergClass.coeff_eq_zero_of_lt_firstIndex (F : ExtendedSelbergClass) {n : ℕ}
    (hn : n < F.firstIndex) : (F.coeff n : ℂ) = 0 := by
  by_contra h
  exact Nat.find_min F.exists_coeff_ne_zero hn h

theorem ExtendedSelbergClass.firstIndex_pos (F : ExtendedSelbergClass) : 0 < F.firstIndex := by
  rcases Nat.eq_zero_or_pos F.firstIndex with h | h
  · have := F.coeff_firstIndex_ne_zero
    rw [h, ArithmeticFunction.map_zero] at this
    exact absurd rfl this
  · exact h

theorem SelbergClass.firstIndex_eq_one (F : SelbergClass) :
    F.toExtendedSelbergClass.firstIndex = 1 := by
  have hpos := F.toExtendedSelbergClass.firstIndex_pos
  have hle : F.toExtendedSelbergClass.firstIndex ≤ 1 :=
    Nat.find_min' _ (by rw [F.coeff_one]; exact one_ne_zero)
  omega

/-! ## The asymmetric functional equation far to the left -/

theorem SelbergGammaData.analyticAt_gammaFactor_of_ne_neg_nat (G : SelbergGammaData) (z : ℂ)
    (hnot : ∀ j, ∀ n : ℕ, (G.lambda j : ℂ) * z + G.mu j ≠ -(n : ℂ)) :
    AnalyticAt ℂ G.gammaFactor z := by
  rw [SelbergGammaData.gammaFactor]
  apply AnalyticAt.mul
  · have hQdiff : Differentiable ℂ fun s : ℂ ↦ (G.Q : ℂ) ^ s :=
      differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr G.Q_pos.ne'))
    exact hQdiff.analyticAt z
  · exact Finset.univ.analyticAt_prod fun j _ ↦ G.analyticAt_gammaAffine_of_ne_neg_nat j z (hnot j)

theorem ne_neg_nat_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
  intro n h
  rw [h] at hw
  simp at hw

theorem ne_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ n : ℕ, w ≠ -(n : ℂ) := by
  intro n h
  rw [h] at hw
  simp only [Complex.neg_re, Complex.natCast_re] at hw
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- A point to the left of the imaginary axis all of whose Gamma arguments are nonreal lies in
the regular set of the asymmetric functional equation. -/
theorem ExtendedSelbergClass.mem_asymmetricFERegularSet_of_im_ne_zero (F : ExtendedSelbergClass)
    {z : ℂ} (hz : z.re < 0)
    (him : ∀ j, ((F.gammaData.lambda j : ℂ) * z + F.gammaData.mu j).im ≠ 0) :
    z ∈ F.asymmetricFERegularSet := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hz
    linarith
  have hrefl1 : 1 - star z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hreflre : ∀ j, 0 < ((F.gammaData.lambda j : ℂ) * (1 - star z) + F.gammaData.mu j).re := by
    intro j
    have hl := F.gammaData.lambda_pos j
    have hmu := F.gammaData.mu_re_nonneg j
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re, zero_mul, sub_zero,
      Complex.sub_im, Complex.one_im, Complex.conj_im]
    nlinarith
  refine ⟨⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · unfold selbergCompletedValue
    exact (F.gammaData.analyticAt_gammaFactor_of_ne_neg_nat z
      fun j => ne_neg_nat_of_im_ne_zero (him j)).mul
      (F.continuation.analyticAt_value_of_ne_one hz1)
  · unfold selbergCompletedValue
    exact (F.gammaData.analyticAt_gammaFactor_of_ne_neg_nat _
      fun j => ne_neg_nat_of_re_pos (hreflre j)).mul
      (F.continuation.analyticAt_value_of_ne_one hrefl1)
  · exact Complex.Gamma_ne_zero (ne_neg_nat_of_im_ne_zero (him j))
  · refine Complex.Gamma_ne_zero (ne_neg_nat_of_im_ne_zero ?_)
    have h := him j
    have hrw : (1 - (F.gammaData.lambda j : ℂ) * z - F.gammaData.mu j).im =
        -((F.gammaData.lambda j : ℂ) * z + F.gammaData.mu j).im := by
      simp only [Complex.sub_im, Complex.one_im, Complex.add_im]
      ring
    rw [hrw]
    exact neg_ne_zero.mpr h

theorem eventually_ne_nhdsNE_zero (c : ℝ) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ c := by
  by_cases hc : c = 0
  · subst hc
    exact eventually_mem_nhdsWithin
  · exact (eventually_ne_nhds (Ne.symm hc)).filter_mono nhdsWithin_le_nhds

/-- The asymmetric archimedean factor is continuous at every point where all its Gamma arguments
have positive real part. -/
theorem SelbergGammaData.continuousAt_asymmetricH (G : SelbergGammaData) {s : ℂ}
    (hs : s.re < 1) (hsμ : ∀ j, G.lambda j * s.re < 1 - (G.mu j).re) :
    ContinuousAt G.asymmetricH s := by
  unfold SelbergGammaData.asymmetricH
  have hQ : ContinuousAt (fun z : ℂ => (G.Q : ℂ) ^ (1 - 2 * z)) s := by
    have hQne : (G.Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr G.Q_pos.ne'
    exact ((differentiable_id.const_cpow (.inl hQne)).comp
      (differentiable_const _ |>.sub (differentiable_id.const_mul _))).continuous.continuousAt
  have hprod : ContinuousAt (fun z : ℂ => ∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - z) +
      star (G.mu j)) * Complex.Gamma (1 - (G.lambda j : ℂ) * z - G.mu j)) s := by
    refine tendsto_finsetProd _ fun j _ => ?_
    have hl := G.lambda_pos j
    have hmu := G.mu_re_nonneg j
    have h1 : ∀ n : ℕ, (G.lambda j : ℂ) * (1 - s) + star (G.mu j) ≠ -(n : ℂ) := by
      refine ne_neg_nat_of_re_pos ?_
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re, zero_mul, sub_zero,
        Complex.sub_im, Complex.one_im]
      nlinarith
    have h2 : ∀ n : ℕ, 1 - (G.lambda j : ℂ) * s - G.mu j ≠ -(n : ℂ) := by
      refine ne_neg_nat_of_re_pos ?_
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      linarith [hsμ j]
    have hc1 : ContinuousAt (fun z : ℂ => Complex.Gamma ((G.lambda j : ℂ) * (1 - z) +
        star (G.mu j))) s :=
      ContinuousAt.comp (g := Complex.Gamma)
        (f := fun z : ℂ => (G.lambda j : ℂ) * (1 - z) + star (G.mu j)) (x := s)
        (Complex.differentiableAt_Gamma _ h1).continuousAt (by fun_prop)
    have hc2 : ContinuousAt (fun z : ℂ => Complex.Gamma (1 - (G.lambda j : ℂ) * z - G.mu j)) s :=
      ContinuousAt.comp (g := Complex.Gamma)
        (f := fun z : ℂ => 1 - (G.lambda j : ℂ) * z - G.mu j) (x := s)
        (Complex.differentiableAt_Gamma _ h2).continuousAt (by fun_prop)
    exact hc1.mul hc2
  exact (continuousAt_const.mul hQ).mul hprod

theorem SelbergGammaData.continuous_asymmetricS (G : SelbergGammaData) :
    Continuous G.asymmetricS := by
  unfold SelbergGammaData.asymmetricS
  exact continuous_const.mul (continuous_finsetProd _ fun j _ => by fun_prop)

theorem ExtendedSelbergClass.continuousAt_value (F : ExtendedSelbergClass) {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt F z :=
  (F.continuation.analyticAt_value_of_ne_one hz).continuousAt

/-- **The asymmetric functional equation holds pointwise far to the left**, including at the
trivial zeros where the Gamma factors of the completed value have poles. -/
theorem ExtendedSelbergClass.value_eq_asymmetric_of_farLeft (F : ExtendedSelbergClass) {s : ℂ}
    (hs : s.re < 0) (hsμ : ∀ j, F.gammaData.lambda j * s.re < 1 - (F.gammaData.mu j).re) :
    F s = F.gammaData.invariantRootNumber * F.gammaData.asymmetricS s *
      F.gammaData.asymmetricH s * selbergConjugateReflection F s := by
  set G := F.gammaData
  let g : ℝ → ℂ := fun t => s + (t : ℂ) * Complex.I
  have hg0 : g 0 = s := by simp [g]
  have hgc : Continuous g := by fun_prop
  -- regular points accumulate at `s` from above and below
  have hreg : ∀ᶠ t in 𝓝[≠] (0 : ℝ), g t ∈ F.asymmetricFERegularSet := by
    have hall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ j,
        ((G.lambda j : ℂ) * g t + G.mu j).im ≠ 0 := by
      refine Filter.eventually_all.2 fun j => ?_
      filter_upwards [eventually_ne_nhdsNE_zero (-(G.mu j).im / G.lambda j - s.im)] with t ht
      have hl := G.lambda_pos j
      simp only [g, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero]
      intro h0
      apply ht
      field_simp
      linarith
    filter_upwards [hall] with t ht
    refine F.mem_asymmetricFERegularSet_of_im_ne_zero ?_ ht
    simpa [g] using hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hrefl1 : 1 - star s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hLHS : ContinuousAt (fun t => F (g t)) 0 := by
    have := F.continuousAt_value hs1
    rw [← hg0] at this
    exact this.comp hgc.continuousAt
  have hRHScont : ContinuousAt (fun z : ℂ => G.invariantRootNumber * G.asymmetricS z *
      G.asymmetricH z * selbergConjugateReflection F z) s := by
    have hH := G.continuousAt_asymmetricH (by linarith) hsμ
    have hR : ContinuousAt (selbergConjugateReflection F) s := by
      unfold selbergConjugateReflection
      have hin : ContinuousAt (fun z : ℂ => 1 - star z) s := by fun_prop
      exact continuous_star.continuousAt.comp (ContinuousAt.comp (g := F)
        (f := fun z : ℂ => 1 - star z) (x := s) (F.continuousAt_value hrefl1) hin)
    exact ((continuousAt_const.mul G.continuous_asymmetricS.continuousAt).mul hH).mul hR
  have hRHS : ContinuousAt (fun t => G.invariantRootNumber * G.asymmetricS (g t) *
      G.asymmetricH (g t) * selbergConjugateReflection F (g t)) 0 := by
    rw [← hg0] at hRHScont
    exact hRHScont.comp hgc.continuousAt
  have hEq : (fun t => F (g t)) =ᶠ[𝓝[≠] (0 : ℝ)] (fun t => G.invariantRootNumber *
      G.asymmetricS (g t) * G.asymmetricH (g t) * selbergConjugateReflection F (g t)) := by
    filter_upwards [hreg] with t ht
    exact F.asymmetricFunctionalEquation_eq_of_mem_regularSet ht
  have h1 := hLHS.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  have h2 := hRHS.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  have := tendsto_nhds_unique (h1.congr' hEq) h2
  simpa [hg0] using this

/-- Along the shift lattice every point is eventually far enough to the left. -/
theorem ExtendedSelbergClass.eventually_farLeft_shift (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    ∀ᶠ k : ℕ in atTop, (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)).re < 0 ∧
      ∀ j, F.gammaData.lambda j * (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)).re <
        1 - (F.gammaData.mu j).re := by
  have hre : ∀ k : ℕ, (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)).re =
      s₀.re - (k : ℝ) / F.gammaData.degree := by
    intro k
    have hkd : ((k : ℂ) / (F.gammaData.degree : ℂ)) =
        ((((k : ℝ) / F.gammaData.degree : ℝ)) : ℂ) := by push_cast; ring
    rw [hkd, Complex.sub_re, Complex.ofReal_re]
  have hbot : Tendsto (fun k : ℕ => (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)).re) atTop atBot := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) / F.gammaData.degree) atTop atTop :=
      Filter.Tendsto.atTop_div_const hd tendsto_natCast_atTop_atTop
    have h2 := tendsto_atBot_add_const_left atTop s₀.re (tendsto_neg_atTop_atBot.comp h1)
    exact h2.congr fun k => by rw [hre k]; simp [sub_eq_add_neg]
  refine (hbot.eventually_lt_atBot 0).and (Filter.eventually_all.2 fun j => ?_)
  have hl := F.gammaData.lambda_pos j
  filter_upwards [hbot.eventually_lt_atBot ((1 - (F.gammaData.mu j).re) / F.gammaData.lambda j)]
    with k hk
  rwa [lt_div_iff₀ hl, mul_comm] at hk

/-! ## The sine factor does not vanish on `2r+1` consecutive lattice points -/

/-- The zeros of one sine factor along the lattice, among the first `N+1` indices, number at most
`N λ_j/d + 1`: they inject into the integers of an interval of that length. -/
theorem SelbergGammaData.card_sine_zeros_shift_le (G : SelbergGammaData) (hd : 0 < G.degree)
    (s₀ : ℂ) (j : Fin G.rank) (N : ℕ) :
    (((Finset.range (N + 1)).filter fun k : ℕ => Complex.sin ((Real.pi : ℂ) *
        ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)) = 0).card : ℝ) ≤
      N * G.lambda j / G.degree + 1 := by
  classical
  set c : ℝ := G.lambda j * s₀.re + (G.mu j).re with hc
  set L : ℝ := N * G.lambda j / G.degree with hL
  have hl := G.lambda_pos j
  have hLnn : 0 ≤ L := by positivity
  -- the real part of the sine argument at index `k`
  have hval : ∀ k : ℕ, ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j).re =
      c - G.lambda j * k / G.degree := by
    intro k
    have hkd : ((k : ℂ) / (G.degree : ℂ)) = ((((k : ℝ) / G.degree : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hkd]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, hc]
    ring
  -- at a zero the argument is an integer
  have hint : ∀ k : ℕ, Complex.sin ((Real.pi : ℂ) *
      ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)) = 0 →
      ((⌊c - G.lambda j * k / G.degree⌋ : ℤ) : ℝ) = c - G.lambda j * k / G.degree := by
    intro k hk
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.1 hk
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have harg : (G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j = n := by
      have := hn
      rw [mul_comm ((n : ℂ))] at this
      exact mul_left_cancel₀ hpi this
    have hre := congrArg Complex.re harg
    rw [hval k, Complex.intCast_re] at hre
    rw [hre, Int.floor_intCast]
  set K := (Finset.range (N + 1)).filter fun k : ℕ => Complex.sin ((Real.pi : ℂ) *
    ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)) = 0 with hK
  have hmaps : Set.MapsTo (fun k : ℕ => ⌊c - G.lambda j * k / G.degree⌋) (K : Set ℕ)
      (Finset.Icc ⌈c - L⌉ ⌊c⌋ : Set ℤ) := by
    intro k hk
    rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk
    have heq := hint k hk.2
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 hk.1
    have hlow : c - L ≤ c - G.lambda j * k / G.degree := by
      rw [hL]
      have : G.lambda j * k / G.degree ≤ N * G.lambda j / G.degree := by
        rw [div_le_div_iff_of_pos_right hd]
        nlinarith
      linarith
    have hhigh : c - G.lambda j * k / G.degree ≤ c := by
      have : 0 ≤ G.lambda j * k / G.degree := by positivity
      linarith
    rw [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rw [Int.ceil_le, heq]
      exact hlow
    · rw [Int.le_floor, heq]
      exact hhigh
  have hinj : Set.InjOn (fun k : ℕ => ⌊c - G.lambda j * k / G.degree⌋) (K : Set ℕ) := by
    intro k hk k' hk' hkk'
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hk hk'
    have h1 := hint k hk.2
    have h2 := hint k' hk'.2
    have hreal : c - G.lambda j * k / G.degree = c - G.lambda j * k' / G.degree := by
      rw [← h1, ← h2]
      exact congrArg _ hkk'
    have hdiv : G.lambda j * k / G.degree = G.lambda j * k' / G.degree := by linarith
    have hmul : G.lambda j * (k : ℝ) = G.lambda j * k' := (div_left_inj' hd.ne').1 hdiv
    exact_mod_cast mul_left_cancel₀ hl.ne' hmul
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at hcard
  have hcardR : (K.card : ℝ) ≤ ((⌊c⌋ + 1 - ⌈c - L⌉).toNat : ℝ) := by exact_mod_cast hcard
  have hnn : 0 ≤ ⌊c⌋ + 1 - ⌈c - L⌉ := by
    have h1 : (⌈c - L⌉ : ℝ) < c - L + 1 := Int.ceil_lt_add_one _
    have h2 : c - 1 < (⌊c⌋ : ℝ) := Int.sub_one_lt_floor _
    have hR : ((-1 : ℤ) : ℝ) < ((⌊c⌋ + 1 - ⌈c - L⌉ : ℤ) : ℝ) := by
      push_cast
      linarith
    have : (-1 : ℤ) < ⌊c⌋ + 1 - ⌈c - L⌉ := by exact_mod_cast hR
    omega
  rw [show (((⌊c⌋ + 1 - ⌈c - L⌉).toNat : ℕ) : ℝ) = ((⌊c⌋ + 1 - ⌈c - L⌉ : ℤ) : ℝ) by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]] at hcardR
  push_cast at hcardR
  have h1 : c - L ≤ (⌈c - L⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌊c⌋ : ℝ) ≤ c := Int.floor_le _
  linarith

/-- **The sine factor is nonzero somewhere among the first `2r+1` lattice points.** -/
theorem SelbergGammaData.exists_asymmetricS_shift_ne_zero (G : SelbergGammaData)
    (hd : 0 < G.degree) (s₀ : ℂ) :
    ∃ k₀ : ℕ, G.asymmetricS (s₀ - (k₀ : ℂ) / (G.degree : ℂ)) ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  set N : ℕ := 2 * G.rank
  have hcover : Finset.range (N + 1) ⊆ Finset.univ.biUnion fun j : Fin G.rank =>
      (Finset.range (N + 1)).filter fun k : ℕ => Complex.sin ((Real.pi : ℂ) *
        ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)) = 0 := by
    intro k hk
    have hS := hall k
    unfold SelbergGammaData.asymmetricS at hS
    rcases mul_eq_zero.1 hS with h2 | hprod
    · exact absurd h2 (pow_ne_zero _ two_ne_zero)
    · obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hprod
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, Finset.mem_filter.2 ⟨hk, hj⟩⟩
  have hcard := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  rw [Finset.card_range] at hcard
  have hcardR : ((N + 1 : ℕ) : ℝ) ≤ ∑ j : Fin G.rank, ((((Finset.range (N + 1)).filter
      fun k : ℕ => Complex.sin ((Real.pi : ℂ) * ((G.lambda j : ℂ) *
        (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)) = 0).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hbound := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    G.card_sine_zeros_shift_le hd s₀ j N
  have hsum : ∑ j : Fin G.rank, ((N : ℝ) * G.lambda j / G.degree + 1) =
      (N : ℝ) / 2 + G.rank := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.sum_div, ← Finset.mul_sum]
    have hdeg : G.degree = 2 * ∑ j, G.lambda j := rfl
    rw [hdeg]
    have hpos : 0 < ∑ j, G.lambda j := by
      have : 0 < 2 * ∑ j, G.lambda j := hd
      linarith
    field_simp
  rw [hsum] at hbound
  have hN : (N : ℝ) = 2 * G.rank := by simp [N]
  push_cast at hcardR
  linarith

/-- **The sine factor is frequently bounded below along the lattice, at every base point.** -/
theorem SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift_everywhere
    (G : SelbergGammaData)
    (hd : 0 < G.degree) (s₀ : ℂ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ := by
  obtain ⟨k₀, hk₀⟩ := G.exists_asymmetricS_shift_ne_zero hd s₀
  obtain ⟨c₀, hc₀, hfreq⟩ := G.exists_frequently_le_norm_asymmetricS_shift_of_ne_zero hd _ hk₀
  refine ⟨c₀, hc₀, Filter.frequently_atTop.2 fun L => ?_⟩
  obtain ⟨k, hk, hkc⟩ := Filter.frequently_atTop.1 hfreq L
  refine ⟨k₀ + k, by omega, ?_⟩
  have hpt : s₀ - (k₀ : ℂ) / (G.degree : ℂ) - (k : ℂ) / (G.degree : ℂ) =
      s₀ - ((k₀ + k : ℕ) : ℂ) / (G.degree : ℂ) := by
    push_cast
    ring
  rwa [hpt] at hkc

/-! ## The reflected series at its first index -/

/-- The reflected Dirichlet series along the lattice has `k`-th root `m₀^{-1/d}`. -/
theorem ExtendedSelbergClass.tendsto_norm_reflection_shift_rpow_inv (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    Tendsto (fun k : ℕ =>
        ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ ^ (1 / (k : ℝ)))
      atTop (𝓝 ((F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)))) := by
  set d := F.gammaData.degree with hddef
  set m := F.firstIndex with hmdef
  have hm := F.firstIndex_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => (F.coeff n : ℂ)) ((4 : ℝ) : ℂ) n‖) :=
    summable_norm_term_of_rpow_bound hC (by norm_num)
  set w : ℕ → ℂ := fun k => 1 - star (s₀ - (k : ℂ) / (d : ℂ)) with hw
  have hkd : ∀ k : ℕ, ((k : ℂ) / (d : ℂ)) = ((((k : ℝ) / d : ℝ)) : ℂ) := by
    intro k; push_cast; ring
  have hre : ∀ k : ℕ, (w k).re = 1 - s₀.re + (k : ℝ) / d := by
    intro k
    rw [hw]
    simp only [hkd k]
    simp
    ring
  have hatTop : Tendsto (fun k : ℕ => (w k).re) atTop atTop := by
    have hbase : Tendsto (fun k : ℕ => (k : ℝ) / d) atTop atTop :=
      Filter.Tendsto.atTop_div_const hd tendsto_natCast_atTop_atTop
    exact (Filter.tendsto_atTop_add_const_left atTop (1 - s₀.re) hbase).congr
      fun k => (hre k).symm
  have hLS := tendsto_cpow_mul_LSeries_of_re_atTop hsum hm
    (fun n hn hnm => F.coeff_eq_zero_of_lt_firstIndex hnm) hatTop
  -- the normalized norms tend to `‖a(m)‖ > 0`
  set A : ℝ := ‖(F.coeff m : ℂ)‖ with hA
  have hApos : 0 < A := norm_pos_iff.mpr F.coeff_firstIndex_ne_zero
  have hx : Tendsto (fun k : ℕ =>
      (m : ℝ) ^ (w k).re * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖)
      atTop (𝓝 A) := by
    have h := hLS.norm
    refine h.congr' ?_
    filter_upwards [hatTop.eventually_gt_atTop 1] with k hk
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm, selbergConjugateReflection, norm_star,
      F.lSeries_eq_value (w k) hk]
    rfl
  have hxroot : Tendsto (fun k : ℕ =>
      ((m : ℝ) ^ (w k).re * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖) ^
        (1 / (k : ℝ))) atTop (𝓝 1) := by
    refine tendsto_rpow_inv_of_polynomial_bounds (C₁ := A / 2) (C₂ := 2 * A) (B := 0)
      (by positivity) (by positivity) ?_ ?_
    · filter_upwards [hx.eventually_const_lt (by linarith : A / 2 < A)] with k hk
      rw [neg_zero, Real.rpow_zero, mul_one]
      exact hk.le
    · filter_upwards [hx.eventually_lt_const (by linarith : A < 2 * A)] with k hk
      rw [Real.rpow_zero, mul_one]
      exact hk.le
  have hexp : Tendsto (fun k : ℕ => (m : ℝ) ^ (-(w k).re * (1 / (k : ℝ)))) atTop
      (𝓝 ((m : ℝ) ^ (-(1 / d)))) := by
    have hlim : Tendsto (fun k : ℕ => -(w k).re * (1 / (k : ℝ))) atTop (𝓝 (-(1 / d))) := by
      have h1 : Tendsto (fun k : ℕ => (1 - s₀.re) / (k : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h2 : Tendsto (fun k : ℕ => -((1 - s₀.re) / (k : ℝ)) - 1 / d) atTop
          (𝓝 (-0 - 1 / d)) := (h1.neg).sub_const _
      rw [neg_zero, zero_sub] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [hre k]
      field_simp
      ring
    exact (Real.continuousAt_const_rpow hmR.ne').tendsto.comp hlim
  have hprod := hxroot.mul hexp
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards with k
  have hmpow : (m : ℝ) ^ (w k).re * (m : ℝ) ^ (-(w k).re) = 1 := by
    rw [← Real.rpow_add hmR, add_neg_cancel, Real.rpow_zero]
  rw [Real.rpow_mul hmR.le, ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  calc (m : ℝ) ^ (w k).re * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ *
        (m : ℝ) ^ (-(w k).re)
      = ((m : ℝ) ^ (w k).re * (m : ℝ) ^ (-(w k).re)) *
          ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ := by ring
    _ = _ := by rw [hmpow, one_mul]

/-! ## The law -/

/-- **The cusp growth law, first-index form.**  At every base point the factorially normalized
values along the shift lattice have `k`-th root `limsup` equal to `q^{1/d}/(2πd) · m₀^{-1/d}`. -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_firstIndex (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree) / (2 * Real.pi * F.gammaData.degree) *
        (F.firstIndex : ℝ) ^ (-(1 / F.gammaData.degree)) := by
  set d : ℝ := F.gammaData.degree with hdef
  set κ : ℝ := F.gammaData.conductor ^ (1 / d) / (2 * Real.pi * d) *
    (F.firstIndex : ℝ) ^ (-(1 / d)) with hκdef
  have hmR : (0 : ℝ) < F.firstIndex := by exact_mod_cast F.firstIndex_pos
  have hκ : 0 < κ := by
    have h1 : 0 < F.gammaData.conductor ^ (1 / d) :=
      Real.rpow_pos_of_pos F.gammaData.conductor_pos _
    have h2 : 0 < 2 * Real.pi * d := by positivity
    have h3 : 0 < (F.firstIndex : ℝ) ^ (-(1 / d)) := Real.rpow_pos_of_pos hmR _
    positivity
  have harch := F.gammaData.tendsto_norm_asymmetricH_shift_rpow_inv hd s₀
  have hrefl := F.tendsto_norm_reflection_shift_rpow_inv hd s₀
  have hA : Tendsto (fun k : ℕ =>
      (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ))
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ)))
      atTop (𝓝 κ) := harch.mul hrefl
  obtain ⟨c₀, hc₀, hfreq⟩ := F.gammaData.exists_frequently_le_norm_asymmetricS_shift_everywhere hd s₀
  obtain ⟨B, hB, hBle⟩ := F.gammaData.exists_bound_norm_asymmetricS_shift s₀
  have hnn : ∀ k : ℕ, 0 ≤ ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ :=
    fun k => norm_nonneg _
  have hBlimsup : limsup (fun k : ℕ =>
      ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ))) atTop = 1 :=
    limsup_rpow_inv_eq_one hB hc₀ hnn hBle hfreq
  have hBbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ =>
      ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ ^ (1 / (k : ℝ))) :=
    isBoundedUnder_rpow_inv hB hnn hBle
  have hmain := limsup_mul_eq_of_tendsto hκ hA
    (fun k => Real.rpow_nonneg (norm_nonneg _) _) hBbdd hBlimsup
  rw [← hmain]
  refine limsup_congr ?_
  filter_upwards [F.eventually_farLeft_shift hd s₀] with k ⟨hk0, hkμ⟩
  have hFEk := F.value_eq_asymmetric_of_farLeft hk0 hkμ
  have hnormF : ‖F (s₀ - (k : ℂ) / (d : ℂ))‖
      = ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ := by
    rw [hFEk, norm_mul, norm_mul, norm_mul, F.gammaData.norm_invariantRootNumber, one_mul]
  rw [hnormF]
  have hrearr : ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖
        * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)
      = (‖F.gammaData.asymmetricH (s₀ - (k : ℂ) / (d : ℂ))‖ / (k.factorial : ℝ)
          * ‖selbergConjugateReflection F (s₀ - (k : ℂ) / (d : ℂ))‖)
        * ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (d : ℂ))‖ := by
    ring
  rw [hrearr, Real.mul_rpow (by positivity) (norm_nonneg _),
    Real.mul_rpow (by positivity) (norm_nonneg _)]

/-- The first-index constant is the reciprocal of `2π` times the cusp gap. -/
theorem cuspConstant_firstIndex_eq {d q : ℝ} (hd : 0 < d) (hq : 0 < q) {m : ℝ} (hm : 0 < m) :
    q ^ (1 / d) / (2 * Real.pi * d) * m ^ (-(1 / d)) =
      1 / (2 * Real.pi * (d * (m / q) ^ (1 / d))) := by
  have hq' : 0 < q ^ (1 / d) := Real.rpow_pos_of_pos hq _
  have hm' : 0 < m ^ (1 / d) := Real.rpow_pos_of_pos hm _
  rw [Real.rpow_neg hm.le, Real.div_rpow hm.le hq.le]
  field_simp

/-- **The cusp growth law.**  For every extended Selberg-class member of positive degree and every
base point, the growth constant of the shift lattice is `1/(2π Δ(0))`, with `Δ(0)` the distance
from the cusp to the standard-twist spectrum. -/
theorem ExtendedSelbergClass.cuspGrowthLaw (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop = 1 / (2 * Real.pi * Metric.infDist 0 F.shiftSpectrum) := by
  rw [F.limsup_norm_shift_rpow_inv_firstIndex hd s₀, ExtendedSelbergClass.shiftSpectrum,
    ExtendedSelbergClass.presentationDegree, ExtendedSelbergClass.presentationConductor,
    infDist_zero_shiftSpectrum_of_first (a := fun n => (F.coeff n : ℂ)) F.firstIndex_pos
      F.coeff_firstIndex_ne_zero (fun n _ hn => F.coeff_eq_zero_of_lt_firstIndex hn) hd
      F.gammaData.conductor_pos]
  exact cuspConstant_firstIndex_eq hd F.gammaData.conductor_pos
    (by exact_mod_cast F.firstIndex_pos)

/-- **The cusp growth law for the Selberg class.**  With `a_F(1) = 1` the growth constant at every
base point is `q^{1/d}/(2πd) = 1/(2π · d q^{-1/d})`. -/
theorem SelbergClass.cuspGrowthLaw (F : SelbergClass) (hd : 0 < F.gammaData.degree) (s₀ : ℂ) :
    limsup (fun k : ℕ =>
        (‖F.toExtendedSelbergClass (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ /
          (k.factorial : ℝ)) ^ (1 / (k : ℝ))) atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree) / (2 * Real.pi * F.gammaData.degree) := by
  rw [F.toExtendedSelbergClass.limsup_norm_shift_rpow_inv_firstIndex hd s₀, F.firstIndex_eq_one,
    Nat.cast_one, Real.one_rpow, mul_one]

end

end RHTower
