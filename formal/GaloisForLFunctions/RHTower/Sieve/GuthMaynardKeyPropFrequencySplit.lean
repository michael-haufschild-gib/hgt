import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionChenGuptaLiBridge
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwoTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45OffDiagonalSplit
import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51

/-!
# The nonzero frequencies of the cubic trace at `q = 1`: `S₁ + S₂ + S₃` (Guth–Maynard (5.5))

The Chen–Gupta–Li form of Proposition 4.6 (`cglProposition46_realAsymptotic_bound`) is stated
through the nonzero-frequency sum of the *non-all-equal* row triples,
`Σ_{m ≠ 0} I'_m` with `I'_m = cglLemma45OffDiagonalFrequencyTerm`.  At modulus `q = 1`, for rows
with distinct times forming the set `W`,

* `I'_m = I_m(W) − |W| I_m({0})` (`cglLemma45OffDiagonalFrequencyTerm_modulusOne`): the all-equal
  triples contribute `N³ ĥ_0(m₁N) ĥ_0(m₂N) ĥ_0(m₃N) = I_m({0})` each;
* splitting `ℤ³ ∖ 0` by the number of nonzero coordinates (`tsum_nonzero_eq_three_carriers`),

`Σ_{m≠0} I'_m = S₁' + (S₂(W) − |W| S₂({0})) + (S₃(W) − |W| S₃({0}))`
(`nonzeroFrequencySum_modulusOne`), where `S₁'` is the Chen–Gupta–Li `S₁` of Proposition 5.1,
`S₂ = gmS2` and `S₃ = allNonzeroCubicSum`.  The one-point sums are bounded uniformly in `N ≥ 1`
(`norm_gmS2_singleton_le`, `norm_allNonzeroCubicSum_singleton_le`), so
`‖Σ_{m≠0} I'_m‖ ≤ ‖S₁'‖ + ‖S₂(W)‖ + ‖S₃(W)‖ + c |W|` (`norm_nonzeroFrequencySum_modulusOne_le`).
-/

set_option autoImplicit false

open Finset Complex
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The off-diagonal coefficient at `q = 1` -/

/-- At `q = 1` a CGL coefficient over `A × (ZMod 1)³` is the row-triple sum of
`N³ ĥ_{t_r − t_s}(m₁N) ĥ_{t_s − t_u}(m₂N) ĥ_{t_u − t_r}(m₃N)` over `A`. -/
theorem sum_frequencyIndex_modulusOne (w : CGLRealSmoothBump) (N : CGLPositiveLength) {R : ℕ}
    (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (A : Finset (Fin R × Fin R × Fin R)) (m : (ℤ × ℤ) × ℤ) :
    ∑ i ∈ ((A ×ˢ Finset.univ) ×ˢ Finset.univ) ×ˢ (Finset.univ : Finset (ZMod modulusOne.value)),
      cglLemma45TripleFrequencyTerm w N modulusOne
        (rows i.1.1.1.1).character (rows i.1.1.1.2.1).character
        (rows i.1.1.1.2.1).character (rows i.1.1.1.2.2).character
        (rows i.1.1.1.2.2).character (rows i.1.1.1.1).character
        ((rows i.1.1.1.1).time - (rows i.1.1.1.2.1).time)
        ((rows i.1.1.1.2.1).time - (rows i.1.1.1.2.2).time)
        ((rows i.1.1.1.2.2).time - (rows i.1.1.1.1).time)
        i.1.1.2 i.1.2 i.2 m =
      ∑ rst ∈ A, (N.value : ℂ) ^ 3 *
        (bumpFourier w.toCGLSmoothBump ((rows rst.1).time - (rows rst.2.1).time) (m.1.1 * N.value) *
          bumpFourier w.toCGLSmoothBump ((rows rst.2.1).time - (rows rst.2.2).time)
            (m.1.2 * N.value) *
          bumpFourier w.toCGLSmoothBump ((rows rst.2.2).time - (rows rst.1).time) (m.2 * N.value)) := by
  classical
  haveI : Unique (ZMod modulusOne.value) := (inferInstance : Unique (ZMod 1))
  simp only [Finset.sum_product, Finset.univ_unique, Finset.sum_singleton,
    cglLemma45TripleFrequencyTerm, cglLemma45CharacterPairFourierTerm_modulusOne]
  refine Finset.sum_congr rfl fun rst _ => ?_
  ring

/-- `I_m({0}) = N³ ĥ_0(m₁N) ĥ_0(m₂N) ĥ_0(m₃N)`. -/
theorem gmIm_singleton_zero (w : CGLRealSmoothBump) (N : ℝ) (m : (ℤ × ℤ) × ℤ) :
    gmIm w N {0} m = (N : ℂ) ^ 3 * (bumpFourier w.toCGLSmoothBump 0 (m.1.1 * N) *
      bumpFourier w.toCGLSmoothBump 0 (m.1.2 * N) * bumpFourier w.toCGLSmoothBump 0 (m.2 * N)) := by
  simp [gmIm, cubicTerm, mul_assoc]

/-- **The off-diagonal coefficient at `q = 1`.**  For rows with distinct times forming `W`,
`I'_m = I_m(W) − R · I_m({0})`. -/
theorem cglLemma45OffDiagonalFrequencyTerm_modulusOne (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (R : ℕ) (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (hinj : Function.Injective fun r => (rows r).time) (m : (ℤ × ℤ) × ℤ) :
    cglLemma45OffDiagonalFrequencyTerm w N modulusOne R rows m =
      gmIm w N.value (Finset.univ.image fun r => (rows r).time) m -
        (R : ℂ) * gmIm w N.value {0} m := by
  classical
  rw [← cglLemma45TraceFrequencyTerm_modulusOne w N R rows hinj m]
  unfold cglLemma45OffDiagonalFrequencyTerm cglLemma45OffDiagonalFrequencyIndex
    cglLemma45TraceFrequencyTerm cglLemma45FrequencyIndex
  rw [sum_frequencyIndex_modulusOne, sum_frequencyIndex_modulusOne,
    ← Finset.sum_filter_add_sum_filter_not (cglCharacterDyadicGramCubicIndexSet R)
      (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2))]
  -- the all-equal triples `(r, r, r)`
  have hdiag : (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => ¬¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)) =
      Finset.univ.image fun r : Fin R => (r, r, r) := by
    ext ⟨a, b, c⟩
    simp only [cglCharacterDyadicGramCubicIndexSet, not_not, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨a, rfl, rfl, rfl⟩
    · rintro ⟨r, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  have hinjd : Set.InjOn (fun r : Fin R => (r, r, r)) ↑(Finset.univ : Finset (Fin R)) :=
    fun a _ b _ h => (Prod.mk.inj h).1
  rw [hdiag, Finset.sum_image hinjd]
  simp only [sub_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    gmIm_singleton_zero, Complex.ofReal_natCast]
  ring

/-! ### Splitting `ℤ³ ∖ 0` by the number of nonzero coordinates -/

/-- Frequencies with all three coordinates nonzero: the carrier of `S₃`. -/
def gmS3Frequency (m : (ℤ × ℤ) × ℤ) : Prop :=
  m.1.1 ≠ 0 ∧ m.1.2 ≠ 0 ∧ m.2 ≠ 0

/-- `ℤ³ ∖ 0` is the disjoint union of the `S₁`, `S₂`, `S₃` carriers. -/
theorem indicator_nonzero_eq (f : (ℤ × ℤ) × ℤ → ℂ) (m : (ℤ × ℤ) × ℤ) :
    Set.indicator {m | m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))} f m =
      Set.indicator {m | cglProposition51S1Frequency m} f m +
        Set.indicator {m | gmS2Frequency m} f m + Set.indicator {m | gmS3Frequency m} f m := by
  classical
  obtain ⟨⟨a, b⟩, c⟩ := m
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_singleton,
    cglProposition51S1Frequency, gmS2Frequency, gmS3Frequency]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp [ha, hb, hc, Prod.ext_iff]

/-- A subtype sum as the sum of an indicator. -/
theorem tsum_subtype_eq_indicator (p : (ℤ × ℤ) × ℤ → Prop) (f : (ℤ × ℤ) × ℤ → ℂ) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // p m}, f m = ∑' m, Set.indicator {m | p m} f m :=
  tsum_subtype {m | p m} f

/-- `Σ_{m ≠ 0} f = Σ_{S₁} f + Σ_{S₂} f + Σ_{S₃} f` for summable `f`. -/
theorem tsum_nonzero_eq_three_carriers {f : (ℤ × ℤ) × ℤ → ℂ} (hf : Summable f) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))}, f m =
      ∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m}, f m +
        ∑' m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m}, f m +
        ∑' m : {m : (ℤ × ℤ) × ℤ // gmS3Frequency m}, f m := by
  rw [tsum_subtype_eq_indicator (fun m => m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))),
    tsum_subtype_eq_indicator cglProposition51S1Frequency, tsum_subtype_eq_indicator gmS2Frequency,
    tsum_subtype_eq_indicator gmS3Frequency, ← (hf.indicator _).tsum_add (hf.indicator _),
    ← ((hf.indicator _).add (hf.indicator _)).tsum_add (hf.indicator _)]
  exact tsum_congr fun m => indicator_nonzero_eq f m

/-- `I_m({0})` is summable over `ℤ³` (it is the trace coefficient of the one-row packet at time
`0`). -/
theorem summable_gmIm_singleton (w : CGLRealSmoothBump) (N : CGLPositiveLength) :
    Summable (gmIm w N.value {0}) := by
  classical
  let rows : Fin 1 → CGLCharacterDyadicRowData modulusOne.value := fun _ => ⟨0, 1⟩
  have hinj : Function.Injective fun r => (rows r).time := fun a b _ => Subsingleton.elim a b
  have himage : (Finset.univ.image fun r => (rows r).time) = {0} := by
    ext x; simp [rows]
  have h := cglLemma45TraceFrequencyTerm_summable w N modulusOne 1 rows
  refine h.congr fun m => ?_
  rw [cglLemma45TraceFrequencyTerm_modulusOne w N 1 rows hinj m, himage]

/-- `S₃` written over the left-nested frequency triples. -/
theorem allNonzeroCubicSum_eq_tsum_subtype (w : CGLRealSmoothBump) (W : Finset ℝ) (N : ℝ) :
    allNonzeroCubicSum w.toCGLSmoothBump W N =
      ∑' m : {m : (ℤ × ℤ) × ℤ // gmS3Frequency m}, gmIm w N W m := by
  classical
  rw [tsum_subtype_eq_indicator gmS3Frequency (gmIm w N W), allNonzeroCubicSum,
    ← (Equiv.prodAssoc ℤ ℤ ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, gmS3Frequency, gmIm, Equiv.prodAssoc_apply]

/-- **The nonzero-frequency sum at `q = 1`.**  For rows with distinct times forming `W`:
`Σ_{m≠0} I'_m = S₁' + (S₂(W) − R S₂({0})) + (S₃(W) − R S₃({0}))`. -/
theorem nonzeroFrequencySum_modulusOne (w : CGLRealSmoothBump) (N : CGLPositiveLength) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value)
    (hinj : Function.Injective fun r => (rows r).time) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
        cglLemma45OffDiagonalNonzeroFrequencyTerm w N modulusOne R rows m =
      cglProposition51S1 w N modulusOne R rows +
        (gmS2 w N.value (Finset.univ.image fun r => (rows r).time) -
          (R : ℂ) * gmS2 w N.value {0}) +
        (allNonzeroCubicSum w.toCGLSmoothBump (Finset.univ.image fun r => (rows r).time) N.value -
          (R : ℂ) * allNonzeroCubicSum w.toCGLSmoothBump {0} N.value) := by
  classical
  have hoff := cglLemma45OffDiagonalFrequencyTerm_summable w N modulusOne R rows
  have hW : Summable (gmIm w N.value (Finset.univ.image fun r => (rows r).time)) := by
    have h := cglLemma45TraceFrequencyTerm_summable w N modulusOne R rows
    exact h.congr fun m => cglLemma45TraceFrequencyTerm_modulusOne w N R rows hinj m
  have h0 := summable_gmIm_singleton w N
  have hpt := cglLemma45OffDiagonalFrequencyTerm_modulusOne w N R rows hinj
  -- `Σ_{carrier} (I_m(W) − R I_m({0})) = Σ_{carrier} I_m(W) − R Σ_{carrier} I_m({0})`
  have hcarrier : ∀ p : (ℤ × ℤ) × ℤ → Prop,
      ∑' m : {m : (ℤ × ℤ) × ℤ // p m}, cglLemma45OffDiagonalFrequencyTerm w N modulusOne R rows m =
        ∑' m : {m : (ℤ × ℤ) × ℤ // p m},
            gmIm w N.value (Finset.univ.image fun r => (rows r).time) m -
          (R : ℂ) * ∑' m : {m : (ℤ × ℤ) × ℤ // p m}, gmIm w N.value {0} m := by
    intro p
    have hs1 : Summable fun m : {m : (ℤ × ℤ) × ℤ // p m} =>
        gmIm w N.value (Finset.univ.image fun r => (rows r).time) m :=
      hW.comp_injective Subtype.val_injective
    have hs2 : Summable fun m : {m : (ℤ × ℤ) × ℤ // p m} => (R : ℂ) * gmIm w N.value {0} m :=
      (h0.comp_injective Subtype.val_injective).mul_left _
    rw [tsum_congr fun m : {m : (ℤ × ℤ) × ℤ // p m} => hpt m.1, hs1.tsum_sub hs2, tsum_mul_left]
  change ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
    cglLemma45OffDiagonalFrequencyTerm w N modulusOne R rows m = _
  rw [tsum_nonzero_eq_three_carriers hoff, hcarrier gmS2Frequency, hcarrier gmS3Frequency,
    allNonzeroCubicSum_eq_tsum_subtype, allNonzeroCubicSum_eq_tsum_subtype]
  rfl

/-! ### The one-point sums are bounded -/

/-- `|ĥ_0(0)| ≤ B₀`. -/
theorem norm_bumpFourier_zero_le (w : CGLSmoothBump) :
    ‖bumpFourier w 0 0‖ ≤ cglSmoothBumpHtAllOrderBudget w 0 := by
  have h := cglSmoothBumpHt_allOrder_fourier_decay w 0 0 0
  simpa [bumpFourier] using h

/-- `|S₂({0})| ≤ 3 c_d² B₀` for `N ≥ 1`. -/
theorem norm_gmS2_singleton_le (w : CGLRealSmoothBump) {N : ℝ} (hN : 1 ≤ N) :
    ‖gmS2 w N {0}‖ ≤ 3 * gmDiagConst w ^ 2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 := by
  rw [gmS2_eq_three_mul w (by linarith) {0}]
  simp only [Finset.sum_singleton, gmS2Kernel, sub_self]
  have hA := cube_normSq_gmNonzero_zero_le w hN
  have hB := norm_bumpFourier_zero_le w.toCGLSmoothBump
  have hN0 : (0 : ℝ) ≤ N := by linarith
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hN0]
  have e : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have h0 : 0 ≤ ‖gmHat w 0 0‖ := norm_nonneg _
  have hc : 0 ≤ gmDiagConst w ^ 2 := sq_nonneg _
  calc 3 * (N ^ 3 * (‖gmNonzero w N 0‖ * ‖gmNonzero w N 0‖ * ‖gmHat w 0 0‖))
      = 3 * ((N ^ 3 * ‖gmNonzero w N 0‖ ^ 2) * ‖gmHat w 0 0‖) := by ring
    _ ≤ 3 * (gmDiagConst w ^ 2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0) := by
        gcongr
    _ = _ := by ring

/-- `|S₃({0})| ≤ C` uniformly in `N ≥ 1`. -/
theorem norm_allNonzeroCubicSum_singleton_le (w : CGLSmoothBump) :
    ∃ C, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ‖allNonzeroCubicSum w {0} N‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := norm_allNonzeroCubicSum_sub_box_le w (le_refl 2)
  refine ⟨C, hC0, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have h := hC 0 N {0} 0 le_rfl hN0 (fun t ht => by simp at ht; simp [ht])
  have hbox : ∑ m ∈ nonzeroFrequencyBox 0, cubicTerm w {0} N m.1 m.2.1 m.2.2 = 0 :=
    Finset.sum_eq_zero fun m hm => by
      obtain ⟨⟨h1, -, -⟩, h2, -, -⟩ := mem_nonzeroFrequencyBox.mp hm
      exact absurd (abs_nonpos_iff.mp (by exact_mod_cast h2)) h1
  rw [hbox, sub_zero] at h
  have key : C * N ^ 3 * ((1 : ℝ) / N) ^ 6 ≤ C := by
    rw [div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)]
    have : N ^ 3 ≤ N ^ 6 := pow_le_pow_right₀ hN (by norm_num)
    nlinarith
  calc ‖allNonzeroCubicSum w {0} N‖ ≤ _ := h
    _ = C * N ^ 3 * ((1 : ℝ) / N) ^ 6 := by norm_num
    _ ≤ C := key

/-- **`‖Σ_{m≠0} I'_m‖ ≤ ‖S₁'‖ + ‖S₂(W)‖ + ‖S₃(W)‖ + c R`** at `q = 1`, `N ≥ 1`. -/
theorem norm_nonzeroFrequencySum_modulusOne_le (w : CGLRealSmoothBump) :
    ∃ c, 0 ≤ c ∧ ∀ (N : CGLPositiveLength) (R : ℕ)
      (rows : Fin R → CGLCharacterDyadicRowData modulusOne.value),
      Function.Injective (fun r => (rows r).time) →
      ‖∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm w N modulusOne R rows m‖ ≤
        ‖cglProposition51S1 w N modulusOne R rows‖ +
          ‖gmS2 w N.value (Finset.univ.image fun r => (rows r).time)‖ +
          ‖allNonzeroCubicSum w.toCGLSmoothBump (Finset.univ.image fun r => (rows r).time) N.value‖ +
          c * R := by
  obtain ⟨C₃, hC₃, h₃⟩ := norm_allNonzeroCubicSum_singleton_le w.toCGLSmoothBump
  have hB0 : 0 ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 :=
    (norm_nonneg _).trans (norm_bumpFourier_zero_le w.toCGLSmoothBump)
  refine ⟨3 * gmDiagConst w ^ 2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 + C₃,
    by positivity, fun N R rows hinj => ?_⟩
  have hN : (1 : ℝ) ≤ N.value := by exact_mod_cast N.positive
  rw [nonzeroFrequencySum_modulusOne w N R rows hinj]
  have h2 := norm_gmS2_singleton_le w hN
  have h3 := h₃ N.value hN
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hRn : ‖(R : ℂ)‖ = R := by simp
  refine norm_add₃_le.trans ?_
  have hs2 := norm_sub_le (gmS2 w N.value (Finset.univ.image fun r => (rows r).time))
    ((R : ℂ) * gmS2 w N.value {0})
  have hs3 := norm_sub_le
    (allNonzeroCubicSum w.toCGLSmoothBump (Finset.univ.image fun r => (rows r).time) N.value)
    ((R : ℂ) * allNonzeroCubicSum w.toCGLSmoothBump {0} N.value)
  rw [norm_mul, hRn] at hs2 hs3
  nlinarith [mul_le_mul_of_nonneg_left h2 hR, mul_le_mul_of_nonneg_left h3 hR]

end

end RHTower.GuthMaynard
