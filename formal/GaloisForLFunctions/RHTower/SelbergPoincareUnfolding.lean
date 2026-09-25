import GaloisForLFunctions.RHTower.SelbergPoincareSeries
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding
import GaloisForLFunctions.RHTower.SarnakXuePretrace

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise

/-!
# Unfolding the Poincaré series of `Γ(N)`

For `N ≥ 3` the cell `cellP N` is a fundamental domain of `Γ(N)` (`isFundamentalDomain_cellP_Gamma`), the strip
`0 ≤ Re z < N` is one for `Γ∞(N) = ⟨T^N⟩` (`isFundamentalDomain_stripN`), and translates of `cellP N` by coset
representatives form another fundamental domain of `Γ∞(N)`. The general unfolding identity
`∫_{⋃ R_i F} f = ∫_F Σ_i f(R_i x)` (`integral_iUnion_eq_integral_tsum`) then gives
`∫_{cellP} P_m(z,s) g(z) dμ = ∫_{strip} Im(z)^s e(mz/N) g(z) dμ` for `Γ(N)`-invariant `g`
(`poincare_unfold`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareUnfolding

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SelbergPoincare
open CongruenceSubgroup Matrix.SpecialLinearGroup

variable (N : ℕ)

instance : MeasurableConstSMul (Gamma N) ℍ := ⟨fun h => measurable_const_smul (h : SL(2, ℤ))⟩
instance : SMulInvariantMeasure (Gamma N) ℍ volume :=
  ⟨fun h _ hs => SMulInvariantMeasure.measure_preimage_smul (h : SL(2, ℤ)) hs⟩
instance : MeasurableConstSMul (Hinf N) ℍ := ⟨fun h => measurable_const_smul (h : Gamma N)⟩
instance : SMulInvariantMeasure (Hinf N) ℍ volume :=
  ⟨fun h _ hs => SMulInvariantMeasure.measure_preimage_smul (h : Gamma N) hs⟩

/-- The strip `0 ≤ Re z < N`. -/
def stripN : Set ℍ := {z | 0 ≤ z.re ∧ z.re < N}

theorem measurableSet_stripN : MeasurableSet (stripN N) :=
  measurableSet_Ico.preimage continuous_re.measurable

theorem Hinf_smul (h : Hinf N) (z : ℍ) : ∃ k : ℤ, h • z = T ^ ((N : ℤ) * k) • z := by
  obtain ⟨k, hk⟩ := mem_Hinf N h.2
  exact ⟨k, by rw [Subgroup.smul_def, Subgroup.smul_def, hk]⟩

/-- The strip is a fundamental domain for `⟨T^N⟩`. -/
theorem isFundamentalDomain_stripN [hN : NeZero N] : IsFundamentalDomain (Hinf N) (stripN N) volume where
  nullMeasurableSet := (measurableSet_stripN N).nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun z => by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN.out
    set k := ⌊z.re / N⌋
    let g : Gamma N := ⟨T ^ (N : ℤ), T_pow_mem N⟩
    refine ⟨⟨g ^ (-k), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show ((g ^ (-k) : Gamma N) : SL(2, ℤ)) • z ∈ stripN N
    rw [Subgroup.coe_zpow, ← zpow_mul]
    simp only [stripN, mem_setOf_eq, re_T_zpow_smul]
    have h0 := Int.floor_le (z.re / N)
    have h1 := Int.lt_floor_add_one (z.re / N)
    rw [le_div_iff₀ hN0] at h0
    rw [div_lt_iff₀ hN0] at h1
    push_cast
    constructor <;> nlinarith
  aedisjoint := by
    intro a b hab
    show volume (a • stripN N ∩ b • stripN N) = 0
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN.out
    obtain ⟨n, hn⟩ := mem_Hinf N a.2
    obtain ⟨m, hm⟩ := mem_Hinf N b.2
    have ha : ∀ w : ℍ, (a • w).re = w.re + N * n := by
      intro w; rw [Subgroup.smul_def, Subgroup.smul_def, hn, re_T_zpow_smul]; push_cast; ring
    have hb : ∀ w : ℍ, (b • w).re = w.re + N * m := by
      intro w; rw [Subgroup.smul_def, Subgroup.smul_def, hm, re_T_zpow_smul]; push_cast; ring
    have : a • stripN N ∩ b • stripN N = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨w, hw, rfl⟩ ⟨w', hw', heq⟩
      have heq' : b • w' = a • w := heq
      have key : w.re + N * n = w'.re + N * m := by rw [← ha, ← hb, heq']
      have hw1 : 0 ≤ w.re ∧ w.re < N := hw
      have hw2 : 0 ≤ w'.re ∧ w'.re < N := hw'
      have hnm : n = m := by
        have h3 : (N : ℝ) * n < N * (m + 1) := by nlinarith
        have h4 : (N : ℝ) * m < N * (n + 1) := by nlinarith
        have h3' : (n : ℝ) < m + 1 := lt_of_mul_lt_mul_left h3 hN0.le
        have h4' : (m : ℝ) < n + 1 := lt_of_mul_lt_mul_left h4 hN0.le
        have : n < m + 1 := by exact_mod_cast h3'
        have : m < n + 1 := by exact_mod_cast h4'
        omega
      exact hab (Subtype.ext (Subtype.ext (by rw [hn, hm, hnm])))
    rw [this, measure_empty]

open GaloisForLFunctions.RHTower.SarnakXuePretrace in
/-- `cellP N` is a fundamental domain for `Γ(N)` itself when `N ≥ 3`. -/
theorem isFundamentalDomain_cellP_Gamma (hN : 3 ≤ N) :
    IsFundamentalDomain (Gamma N) (cellP N) volume := by
  have hF := isFundamentalDomain_cellP N
  have hsmul : ∀ (g : Gamma N) (x : ℍ), g • x = (QuotientGroup.mk (g : SL(2, ℤ)) : PSL2Z) • x := by
    intro g x; rw [PSL2Z_mk_smul]; rfl
  have hmem : ∀ g : Gamma N, (QuotientGroup.mk (g : SL(2, ℤ)) : PSL2Z) ∈ gammaBar N :=
    fun g => ⟨g, g.2, rfl⟩
  have hinj : ∀ g h : Gamma N, (QuotientGroup.mk (g : SL(2, ℤ)) : PSL2Z) = QuotientGroup.mk (h : SL(2, ℤ)) →
      g = h := by
    intro g h e
    rw [QuotientGroup.eq, mem_modularActionKernel_iff] at e
    rcases e with e | e
    · exact Subtype.ext (inv_mul_eq_one.mp e)
    · exfalso
      have hm : (g : SL(2, ℤ))⁻¹ * h ∈ Gamma N := mul_mem (inv_mem g.2) h.2
      rw [e, Gamma_mem] at hm
      have h1 := hm.1
      simp at h1
      have : ((2 : ℤ) : ZMod N) = 0 := by
        have : ((-1 : ℤ) : ZMod N) = 1 := by exact_mod_cast h1
        push_cast at this ⊢; linear_combination -this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      have := Int.le_of_dvd (by norm_num) this
      omega
  refine ⟨hF.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [hF.ae_covers] with x hx
    obtain ⟨⟨h, γ, hγ, rfl⟩, hh⟩ := hx
    exact ⟨⟨γ, hγ⟩, by rw [hsmul]; exact hh⟩
  · intro g h hgh
    have hne : (⟨_, hmem g⟩ : gammaBar N) ≠ ⟨_, hmem h⟩ := fun e => hgh (hinj g h (congrArg Subtype.val e))
    have := hF.aedisjoint hne
    have e1 : g • cellP N = (⟨_, hmem g⟩ : gammaBar N) • cellP N := by
      ext x; simp only [mem_smul_set]; constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by rw [hsmul]; rfl⟩
    have e2 : h • cellP N = (⟨_, hmem h⟩ : gammaBar N) • cellP N := by
      ext x; simp only [mem_smul_set]; constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by rw [hsmul]; rfl⟩
    show AEDisjoint volume (g • cellP N) (h • cellP N)
    rw [e1, e2]; exact this

section unfold
open Function
variable {G α ι E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α}
  [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Countable G] [Countable ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Countable G] [Countable ι] in
theorem setIntegral_smul (g : G) (F : Set α) (f : α → E) :
    ∫ x in g • F, f x ∂μ = ∫ x in F, f (g • x) ∂μ := by
  rw [← image_smul]
  exact (measurePreserving_smul g μ).setIntegral_image_emb (measurableEmbedding_const_smul g) f F

omit [Countable G] in
/-- **Unfolding.** If `F` is a fundamental domain for `G` and `R` is injective with pairwise distinct
translates, then `∫_{⋃ R_i F} f = ∫_F Σ_i f(R_i x)` whenever `f` is integrable on the union. -/
theorem integral_iUnion_eq_integral_tsum {F : Set α} (hF : IsFundamentalDomain G F μ) {R : ι → G}
    (hR : Function.Injective R) {f : α → E} (hf : IntegrableOn f (⋃ i, R i • F) μ) :
    ∫ x in ⋃ i, R i • F, f x ∂μ = ∫ x in F, ∑' i, f (R i • x) ∂μ := by
  have hm : ∀ i, NullMeasurableSet (R i • F) μ := fun i => hF.nullMeasurableSet_smul (R i)
  have hd : Pairwise (AEDisjoint μ on fun i => R i • F) := fun i j hij => hF.aedisjoint (hR.ne hij)
  rw [integral_iUnion_ae hm hd hf]
  simp_rw [setIntegral_smul]
  have hint : ∀ i, Integrable (fun x => f (R i • x)) (μ.restrict F) := by
    intro i
    have h := hf.mono_set (subset_iUnion (fun i => R i • F) i)
    rw [IntegrableOn, ← image_smul] at h
    exact ((measurePreserving_smul (R i) μ).restrict_image_emb (measurableEmbedding_const_smul (R i)) F
      ).integrable_comp_emb (measurableEmbedding_const_smul (R i)) |>.mpr h
  have hnorm : HasSum (fun i => ∫ x in F, ‖f (R i • x)‖ ∂μ) (∫ x in ⋃ i, R i • F, ‖f x‖ ∂μ) := by
    have := hasSum_integral_iUnion_ae hm hd hf.norm
    simp_rw [setIntegral_smul] at this
    exact this
  exact integral_tsum_of_summable_integral_norm hint hnorm.summable

end unfold

open GaloisForLFunctions.RHTower.SarnakXuePretrace in
/-- **Unfolding of the Poincaré series.** For `N ≥ 3`, a `Γ(N)`-invariant `g` and `f = Im(z)^s e(mz/N) g`
integrable on the strip `0 ≤ x < N`, `∫_{cellP} P_m(z, s) g(z) dμ = ∫_{strip} Im(z)^s e(mz/N) g(z) dμ`. -/
theorem poincare_unfold [NeZero N] (hN : 3 ≤ N) (m : ℕ) (s : ℂ) {g : ℍ → ℂ}
    (hg : ∀ (γ : Gamma N) z, g ((γ : SL(2, ℤ)) • z) = g z)
    (hint : IntegrableOn (fun z => term N m s z 1 * g z) (stripN N)) :
    ∫ z in cellP N, poincare N m s z * g z = ∫ z in stripN N, term N m s z 1 * g z := by
  set f : ℍ → ℂ := fun z => term N m s z 1 * g z
  have hfinv : ∀ (h : Hinf N) z, f (h • z) = f z := by
    intro h z
    simp only [f]
    rw [show h • z = ((h : Gamma N) : SL(2, ℤ)) • z from rfl, term_smul, hg, one_mul]
    have := term_Hinf N m s z h.2 1 (Nat.pos_of_ne_zero (NeZero.ne N))
    rw [mul_one] at this
    rw [this]
  have hGF := isFundamentalDomain_cellP_Gamma N hN
  set Rep : GaloisForLFunctions.RHTower.SelbergPoincare.Cosets N → Gamma N := fun q => Quotient.out q
  have hU : IsFundamentalDomain (Hinf N) (⋃ q, Rep q • cellP N) volume := by
    apply isFundamentalDomain_iUnion_smul_of_cosetReps hGF (Hinf N) Rep
    · intro g'
      set c : GaloisForLFunctions.RHTower.SelbergPoincare.Cosets N := Quotient.mk _ g'
      have hc : QuotientGroup.rightRel (Hinf N) (Quotient.out c) g' := Quotient.mk_out (s := _) g'
      have hmem : g' * (Quotient.out c)⁻¹ ∈ Hinf N := QuotientGroup.rightRel_apply.mp hc
      exact ⟨⟨_, hmem⟩, c, by simp [Rep]⟩
    · intro h h' c c' heq
      have hcc : c = c' := by
        rw [← Quotient.out_eq c, ← Quotient.out_eq c']
        apply Quotient.sound
        show QuotientGroup.rightRel (Hinf N) _ _
        rw [QuotientGroup.rightRel_apply]
        have : Quotient.out c' * (Quotient.out c)⁻¹ = (h' : Gamma N)⁻¹ * h := by
          calc Quotient.out c' * (Quotient.out c)⁻¹
              = (h' : Gamma N)⁻¹ * ((h' : Gamma N) * Quotient.out c') * (Quotient.out c)⁻¹ := by group
            _ = (h' : Gamma N)⁻¹ * ((h : Gamma N) * Quotient.out c) * (Quotient.out c)⁻¹ := by
                rw [heq]
            _ = _ := by group
        rw [this]
        exact mul_mem (inv_mem h'.2) h.2
      subst hcc
      exact ⟨Subtype.ext (mul_right_cancel heq), rfl⟩
  have hRinj : Function.Injective Rep := by
    intro q q' h
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    simp only [Rep] at h
    rw [h]
  have hintU : IntegrableOn f (⋃ q, Rep q • cellP N) :=
    (hU.integrableOn_iff (isFundamentalDomain_stripN N) hfinv).mpr hint
  rw [(isFundamentalDomain_stripN N).setIntegral_eq hU hfinv,
    integral_iUnion_eq_integral_tsum hGF hRinj hintU]
  congr 1
  funext z
  simp only [f, poincare]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro q
  rw [show Rep q • z = ((Rep q : Gamma N) : SL(2, ℤ)) • z from rfl, term_smul, one_mul, hg]
  congr 1
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

end GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
