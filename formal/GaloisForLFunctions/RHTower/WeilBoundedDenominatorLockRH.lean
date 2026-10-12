import GaloisForLFunctions.RHTower.WeilBoundedDenominatorLockPeriodicity
import GaloisForLFunctions.RHTower.PeriodicExpProducerSingleCharacter
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Bounded-denominator locks force the Riemann hypothesis

**Theorem** (`bounded_denominator_lock_riemannHypothesis`).  Let `G` be a Herglotz producer for the
weights `lam`.  Suppose that on the lower critical line

`G(1 − s) = N^{s−½} D(s) G(s)`,   `D(s) = Σ_k P(k) k^{−(s−½)}`,   `Σ |P(k)| < ∞`,

an almost-periodic lock whose rational frequencies `log(k/N)` may lie on both sides of `0`.  Then
the Riemann hypothesis holds.

**Proof.**
1. The Dirichlet coefficients `a = exp⋆(lam/log)` are `N`-periodic, `a(n) = Ψ(n mod N)`
   (`bounded_denominator_lock_periodic`).
2. A periodic Dirichlet exponential carries one character `χ₁`
   (`periodic_exp_single_character`).  So `a = c ⋆ χ₁` with `c` supported on `N`-smooth integers,
   and `F(s) = A(s) L(s, χ₁)` on `Re s > 1`, where `A(s) = Σ c(m) m^{−s}` converges absolutely
   on `Re s > 0`.
3. `G = s(s − 1) Γ_ℝ(s) A(s) L(s, χ₁)` on `Re s > ½`, `s ≠ 1`, by the identity theorem on the two
   quarter planes and continuity across the real axis.
4. `G(1) ≠ 0`, while for `χ₁ ≠ 1` the right side vanishes at `s = 1`.  So `χ₁` is trivial, and
   `L(s, χ₁) = Π_{p | N}(1 − p^{−s}) ζ(s)`.
5. A zero of `ζ` with `½ < Re ρ < 1` would be a zero of `G`, which has none on `Re s > ½`.
-/

open Complex Filter Topology Set

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral CharacterZeroPlanting

noncomputable section

/-! ### Dirichlet series over `N`-smooth integers -/

/-- `n ↦ n^{−y}` as a completely multiplicative function. -/
def rpowHom (y : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-y)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Bounded coefficients supported on `N`-smooth integers converge absolutely on `Re s > 0`. -/
theorem abscissa_smooth_le_zero {N : ℕ} {f : ℕ → ℂ} {B : ℝ} (hB : ∀ n, ‖f n‖ ≤ B)
    (hsupp : ∀ n, n ∉ Nat.factoredNumbers N.primeFactors → f n = 0) :
    LSeries.abscissaOfAbsConv f ≤ 0 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hlt : ∀ {p : ℕ}, p.Prime → ‖rpowHom y p‖ < 1 := by
    intro p hp
    show ‖(p : ℝ) ^ (-y)‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt
    N.primeFactors).1
  have hsI : Summable ((Nat.factoredNumbers N.primeFactors).indicator fun n => ‖rpowHom y n‖) :=
    (summable_subtype_iff_indicator (s := Nat.factoredNumbers N.primeFactors)).mp hs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine Summable.of_norm_bounded (hsI.mul_left B) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact mul_nonneg hB0 (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · by_cases hm : n ∈ Nat.factoredNumbers N.primeFactors
    · rw [Set.indicator_of_mem hm]
      show ‖f n‖ / (n : ℝ) ^ (y : ℂ).re ≤ B * ‖(n : ℝ) ^ (-y)‖
      rw [ofReal_re, Real.norm_of_nonneg (by positivity), Real.rpow_neg (Nat.cast_nonneg _),
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hB n) (by positivity)
    · rw [hsupp n hm, norm_zero, zero_div, Set.indicator_of_notMem hm, mul_zero]

/-! ### The identity theorem on `Re s > ½`, `s ≠ 1` -/

/-- Two functions holomorphic on `Re s > ½` (the second away from `s = 1`) that agree on `Re s > 1`
agree on `Re s > ½`, `s ≠ 1`. -/
theorem eq_of_eq_right_half {G K : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ G s)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → DifferentiableAt ℂ K s)
    (hright : ∀ s : ℂ, 1 < s.re → G s = K s) {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) :
    G ρ = K ρ := by
  -- the identity on a convex open set inside `Re s > ½`, `s ≠ 1`, meeting `Re s > 1`
  have hconvex : ∀ U : Set ℂ, IsOpen U → Convex ℝ U → (∀ s ∈ U, 1 / 2 < s.re ∧ s ≠ 1) →
      ∀ z₀ ∈ U, 1 < z₀.re → Set.EqOn G K U := by
    intro U hUo hUc hUs z₀ hz₀U hz₀
    have hGU : AnalyticOnNhd ℂ G U := DifferentiableOn.analyticOnNhd (f := G)
      (fun s hs => (hG s (hUs s hs).1).differentiableWithinAt) hUo
    have hKU : AnalyticOnNhd ℂ K U := DifferentiableOn.analyticOnNhd (f := K)
      (fun s hs => (hK s (hUs s hs).1 (hUs s hs).2).differentiableWithinAt) hUo
    exact hGU.eqOn_of_preconnected_of_eventuallyEq hKU hUc.isPreconnected hz₀U (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀]
        with s hs using hright s hs)
  have hre_open : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hupper : Set.EqOn G K ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    hconvex _ (hre_open.inter (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _))
      (fun s hs => ⟨hs.1, fun h => by have := hs.2; rw [h] at this; simp at this⟩)
      (2 + I) ⟨by simp; norm_num, by simp⟩ (by simp)
  have hlower : Set.EqOn G K ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.im < 0}) :=
    hconvex _ (hre_open.inter (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _))
      (fun s hs => ⟨hs.1, fun h => by have := hs.2; rw [h] at this; simp at this⟩)
      (2 - I) ⟨by simp; norm_num, by simp⟩ (by simp)
  rcases lt_trichotomy ρ.im 0 with hlt | heq | hgt
  · exact hlower ⟨hρ, hlt⟩
  · have hcont : ContinuousAt (fun s => G s - K s) ρ := ((hG ρ hρ).sub (hK ρ hρ hρ1)).continuousAt
    have hpath : Tendsto (fun δ : ℝ => ρ + (δ : ℂ) * I) (𝓝[>] 0) (𝓝 ρ) := by
      have hc : Continuous (fun δ : ℝ => ρ + (δ : ℂ) * I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 := hcont.tendsto.comp hpath
    have h2 : Tendsto (fun δ : ℝ => G (ρ + (δ : ℂ) * I) - K (ρ + (δ : ℂ) * I)) (𝓝[>] 0)
        (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      rw [hupper ⟨by simpa using hρ, by simpa [heq] using hδ⟩, sub_self])
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  · exact hupper ⟨hρ, hgt⟩

/-! ### The theorem -/

/-- **Bounded-denominator locks force the Riemann hypothesis.** -/
theorem bounded_denominator_lock_riemannHypothesis {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {N : ℕ} [NeZero N] {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (N : ℂ) ^ (lineS τ - 1 / 2) * LSeries P (lineS τ - 1 / 2) * G (lineS τ)) :
    RiemannHypothesis := by
  classical
  obtain ⟨Ψ, hΨ⟩ := bounded_denominator_lock_periodic hsl hΦre hid hGc hGd hG2 hP hlock
  have hℓ : ∀ σ : ℝ, 1 < σ → LSeriesSummable (lamLog lam) σ := fun σ hσ =>
    lseriesSummable_of_le (norm_lamLog_le lam) hsl (by simpa using hσ)
  obtain ⟨χ₁, hχ₁⟩ := periodic_exp_single_character (lamLog_zero lam) (lamLog_one lam) hℓ hΨ
  set a := dirichletExp (lamLog lam) with ha
  set c := charSmoothCoeff Ψ χ₁ with hc
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  /- the coefficient identity `a = c ⋆ χ₁` -/
  set one : ℕ →*₀ ℂ := primeValueTwist (fun _ => 1) with hone
  have hone_apply : ∀ n, n ≠ 0 → one n = 1 := by
    intro n hn
    have h := norm_primeValueTwist_le (v := fun _ => 1) (σ := 0) (fun p _ => by simp) hn
    show (if n = 0 then 0 else n.factorization.prod fun _ k => (1 : ℂ) ^ k) = 1
    rw [if_neg hn]; simp
  have hsec : ∀ χ m, smoothSection Ψ χ one m = charSmoothCoeff Ψ χ m := by
    intro χ m
    unfold smoothSection charSmoothCoeff
    split_ifs with hm
    · rw [hone_apply m (Nat.ne_zero_of_mem_factoredNumbers hm), mul_one]
    · rfl
  have hcoef : ∀ n, n ≠ 0 → a n = LSeries.convolution c (fun r => χ₁ r * one r) n := by
    intro n hn
    have h := periodic_twist_eq_sum_convolution Ψ one hn
    rw [hone_apply n hn, mul_one] at h
    rw [hΨ n hn, h, Finset.sum_eq_single χ₁]
    · congr 1; funext m; exact hsec χ₁ m
    · intro χ _ hχ
      have h0 : smoothSection Ψ χ one = 0 := by
        funext m; rw [hsec χ m, hχ₁ χ hχ m]; rfl
      rw [h0, LSeries.convolution_def]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  /- the Dirichlet series `A` -/
  have hcB : ∀ n, ‖c n‖ ≤ ∑ a, ‖Ψ a‖ := by
    intro n
    simp only [hc, charSmoothCoeff]
    split_ifs
    · exact norm_charSection_le Ψ χ₁ n
    · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcsupp : ∀ n, n ∉ Nat.factoredNumbers N.primeFactors → c n = 0 := by
    intro n hn; simp only [hc, charSmoothCoeff, if_neg hn]
  have habs := abscissa_smooth_le_zero hcB hcsupp
  have hAd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (LSeries c) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | LSeries.abscissaOfAbsConv c < z.re} :=
      isOpen_lt continuous_const (EReal.continuous_coe_iff.mpr Complex.continuous_re)
    exact (LSeries_differentiableOn c).differentiableAt (hopen.mem_nhds
      (habs.trans_lt (by exact_mod_cast hs)))
  have hcS : ∀ s : ℂ, 0 < s.re → LSeriesSummable c s := fun s hs =>
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (habs.trans_lt (by exact_mod_cast hs))
  /- `F = A · L(χ₁)` on `Re s > 1` -/
  have hF : ∀ s : ℂ, 1 < s.re → zetaOf lam s = LSeries c s * DirichletCharacter.LFunction χ₁ s := by
    intro s hs
    have hχS : LSeriesSummable (fun r : ℕ => χ₁ r * one r) s :=
      LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n hn => by
        rw [norm_mul, hone_apply n hn, norm_one, mul_one, sub_self, Real.rpow_zero, mul_one]
        exact DirichletCharacter.norm_le_one χ₁ _⟩
    rw [← (hLa s hs).2, LSeries_congr (fun {n} hn => hcoef n hn) s,
      LSeries_convolution' (hcS s (by linarith)) hχS, DirichletCharacter.LFunction_eq_LSeries χ₁ hs]
    congr 1
    exact LSeries_congr (fun {n} hn => by simp only [hone_apply n hn, mul_one]) s
  set K : ℂ → ℂ := fun s => s * (s - 1) * Gammaℝ s *
    (LSeries c s * DirichletCharacter.LFunction χ₁ s) with hK
  have hGK : ∀ s : ℂ, 1 < s.re → G s = K s := by
    intro s hs
    rw [G_eq_bigG hsl hid hGd hG2 hs, bigG, hF s hs]
  have hKd : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → DifferentiableAt ℂ K s := by
    intro s hs hs1
    have hre : 0 < s.re := by linarith
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (RHTower.TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos hre)).mul
      ((hAd s hre).mul (DirichletCharacter.differentiableAt_LFunction χ₁ s (Or.inl hs1)))
  have hGK_all : ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → G ρ = K ρ := fun ρ hρ hρ1 =>
    eq_of_eq_right_half (fun s hs => (hGd s hs).differentiableAt) hKd hGK hρ hρ1
  /- the character is trivial -/
  have hχ₁ : χ₁ = 1 := by
    by_contra hχ
    have hK1 : ContinuousAt K 1 :=
      (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (RHTower.TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos (by norm_num))).mul
        ((hAd 1 (by norm_num)).mul
          (DirichletCharacter.differentiableAt_LFunction χ₁ 1 (Or.inr hχ)))).continuousAt
    have hK10 : K 1 = 0 := by simp [hK]
    have hpath : Tendsto (fun ε : ℝ => (1 : ℂ) + ε) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1 : ℂ) + ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 := ((hGc 1 (by norm_num)).sub hK1).tendsto.comp hpath
    have h2 : Tendsto (fun ε : ℝ => G (1 + ε) - K (1 + ε)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        rw [hGK _ (by simp; linarith), sub_self])
    have hG1 : G 1 - K 1 = 0 := tendsto_nhds_unique h1 h2
    rw [hK10, sub_zero] at hG1
    exact G_ne_zero hΦd hGd hG2 (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num) hG1
  /- no zero of `ζ` right of `½` -/
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · have hs1 : s ≠ 1 := fun h => h1 (by rw [h]; simp)
    have hKs : K s = 0 := by
      simp only [hK]
      rw [hχ₁, ← DirichletCharacter.LFunctionTrivChar,
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1, hz]
      ring
    exact G_ne_zero hΦd hGd hG2 hs (by rw [hGK_all s hs hs1, hKs])

end

end AbelianTwist

end RHTower
