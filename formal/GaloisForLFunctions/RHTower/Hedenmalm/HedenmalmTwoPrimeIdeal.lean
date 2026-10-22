import GaloisForLFunctions.HTGeometry.PrincipalConormal
import GaloisForLFunctions.RHTower.Deninger.DeningerEntireQuotientCohomology
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeBezout

/-!
# The two centered prime windows generate the Xi ideal

With the Bezout identity `b₂ a₂ + b₃ a₃ = 1` in hand, the two entire window transforms
`hat c_n = a_n Xi_C` generate exactly the principal ideal of `Xi_C` in the algebra of entire
functions.  Consequently the analytic cokernel of the two-prime row map is the Xi comparison
quotient `O(ℂ) / (Xi_C)`.
-/

open Complex Set

namespace RHTower

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace HedenmalmThetaSource

/-- The entire centered multiplier as an element of the entire-function algebra. -/
def entireCenteredMultiplier (n : ℕ) : DeningerEntire :=
  ⟨centeredMultiplierE n, differentiable_centeredMultiplierE n⟩

@[simp] theorem entireCenteredMultiplier_apply (n : ℕ) (z : ℂ) :
    entireCenteredMultiplier n z = centeredMultiplierE n z := rfl

/-- The centered prime window transform `hat c_n = a_n Xi_C` as an entire algebra element. -/
def entireCenteredWindow (n : ℕ) : DeningerEntire :=
  entireCenteredMultiplier n * deningerEntireXi

@[simp] theorem entireCenteredWindow_apply (n : ℕ) (z : ℂ) :
    entireCenteredWindow n z = centeredMultiplierE n z * XiC z := rfl

/-- **The two-prime Bezout identity in the entire-function algebra.** -/
theorem exists_entire_two_prime_bezout :
    ∃ B₂ B₃ : DeningerEntire,
      B₂ * entireCenteredMultiplier 2 + B₃ * entireCenteredMultiplier 3 = 1 := by
  obtain ⟨b₂, b₃, hb₂, hb₃, hid⟩ := exists_two_prime_bezout
  exact ⟨⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩, DeningerEntire.ext fun z => hid z⟩

/-- The two-prime row map `(f₂, f₃) ↦ f₂ hat c₂ + f₃ hat c₃`. -/
def windowRow : DeningerEntire × DeningerEntire →ₗ[DeningerEntire] DeningerEntire where
  toFun p := p.1 * entireCenteredWindow 2 + p.2 * entireCenteredWindow 3
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem windowRow_apply (p : DeningerEntire × DeningerEntire) :
    windowRow p = p.1 * entireCenteredWindow 2 + p.2 * entireCenteredWindow 3 := rfl

/-- **The two prime windows generate the Xi ideal.**  This is the analytic conormal generation
statement: the ideal of the pair of centered prime window transforms is the principal ideal of
`Xi_C`. -/
theorem span_entireCenteredWindow_eq_xiIdeal :
    Ideal.span {entireCenteredWindow 2, entireCenteredWindow 3} = deningerEntireXiIdeal := by
  obtain ⟨B₂, B₃, hB⟩ := exists_entire_two_prime_bezout
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr
        ⟨entireCenteredMultiplier 2, by rw [entireCenteredWindow]; ring⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨entireCenteredMultiplier 3, by rw [entireCenteredWindow]; ring⟩
  · rw [deningerEntireXiIdeal, Ideal.span_singleton_le_iff_mem]
    have hmem₂ : entireCenteredWindow 2 ∈
        Ideal.span {entireCenteredWindow 2, entireCenteredWindow 3} :=
      Ideal.subset_span (by simp)
    have hmem₃ : entireCenteredWindow 3 ∈
        Ideal.span {entireCenteredWindow 2, entireCenteredWindow 3} :=
      Ideal.subset_span (by simp)
    have : deningerEntireXi
        = B₂ * entireCenteredWindow 2 + B₃ * entireCenteredWindow 3 := by
      rw [entireCenteredWindow, entireCenteredWindow]
      calc deningerEntireXi
          = (B₂ * entireCenteredMultiplier 2 + B₃ * entireCenteredMultiplier 3)
              * deningerEntireXi := by rw [hB, one_mul]
        _ = B₂ * (entireCenteredMultiplier 2 * deningerEntireXi)
              + B₃ * (entireCenteredMultiplier 3 * deningerEntireXi) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem₂) (Ideal.mul_mem_left _ _ hmem₃)

/-- **The range of the two-prime row map is the Xi ideal.** -/
theorem range_windowRow : LinearMap.range windowRow = deningerEntireXiIdeal := by
  rw [← span_entireCenteredWindow_eq_xiIdeal]
  refine le_antisymm ?_ ?_
  · rintro x ⟨p, rfl⟩
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨(1, 0), by simp⟩
    · exact ⟨(0, 1), by simp⟩

/-- **The analytic cokernel of the two positive-kernel prime channels is the Xi comparison
quotient.**  This is the cokernel clause `(17)`. -/
def twoPrimeCokernelEquiv :
    (DeningerEntire ⧸ LinearMap.range windowRow) ≃ₗ[DeningerEntire] DeningerEntireH1 :=
  Submodule.quotEquivOfEq _ _ range_windowRow


/-! ### The conormal module of the Xi divisor -/

/-- **Entire functions have no zero divisors.**  If `F` is not identically zero then it may be
cancelled: this is the identity theorem. -/
theorem deningerEntire_cancel {F A B : DeningerEntire} (hF : ∃ z, F z ≠ 0)
    (h : F * A = F * B) : A = B := by
  obtain ⟨z₀, hz₀⟩ := hF
  have hA : Differentiable ℂ (fun z => (A : ℂ → ℂ) z - (B : ℂ → ℂ) z) := A.2.sub B.2
  have hGA : AnalyticOnNhd ℂ (fun z => (A : ℂ → ℂ) z - (B : ℂ → ℂ) z) Set.univ :=
    fun z _ => hA.differentiableOn.analyticAt Filter.univ_mem
  have hpt : ∀ z, (F : ℂ → ℂ) z * ((A : ℂ → ℂ) z - (B : ℂ → ℂ) z) = 0 := by
    intro z
    have hz := congrArg (fun G : DeningerEntire => (G : ℂ → ℂ) z) h
    simp only [deningerEntire_mul_apply] at hz
    rw [mul_sub, hz, sub_self]
  have hnear : ∀ᶠ z in nhds z₀, (fun z => (A : ℂ → ℂ) z - (B : ℂ → ℂ) z) z
      = (fun _ : ℂ => (0 : ℂ)) z := by
    filter_upwards [(F.2.continuous.continuousAt).eventually_ne hz₀] with z hz
    exact (mul_eq_zero.mp (hpt z)).resolve_left hz
  have := hGA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ
    (Set.mem_univ z₀) hnear
  exact DeningerEntire.ext fun z => by
    have := this (Set.mem_univ z)
    simpa [sub_eq_zero] using this

theorem deningerEntireXi_cancel (A B : DeningerEntire)
    (h : deningerEntireXi * A = deningerEntireXi * B) : A = B :=
  deningerEntire_cancel ⟨0, by simpa [deningerEntireXi_apply] using XiC_zero_ne⟩ h

/-- **The conormal module of the Xi divisor is the Xi comparison quotient.**  This is the
identification `I / I^(2 : ℕ) ≃ (O(C)/(Xi_C))[Xi_C]`. -/
def xiConormalEquiv :
    DeningerEntireH1 ≃ₗ[DeningerEntire] deningerEntireXiIdeal.Cotangent :=
  GaloisForLFunctions.HTGeometry.principalCotangentEquiv deningerEntireXi_cancel

theorem entireCenteredWindow_mem_xiIdeal (n : ℕ) :
    entireCenteredWindow n ∈ deningerEntireXiIdeal :=
  Ideal.mem_span_singleton.mpr ⟨entireCenteredMultiplier n, by rw [entireCenteredWindow]; ring⟩

/-- The conormal class of a centered prime window. -/
def windowCotangent (n : ℕ) : deningerEntireXiIdeal.Cotangent :=
  deningerEntireXiIdeal.toCotangent ⟨entireCenteredWindow n, entireCenteredWindow_mem_xiIdeal n⟩

/-- **The two prime window classes generate the conormal module.**  This is the generation clause
`(12)`: `[hat c_2]` and `[hat c_3]` span `I / I^(2 : ℕ)` everywhere. -/
theorem span_windowCotangent_eq_top :
    Submodule.span DeningerEntire {windowCotangent 2, windowCotangent 3} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := deningerEntireXiIdeal.toCotangent_surjective x
  have hy : (y : DeningerEntire) ∈ LinearMap.range windowRow := by
    rw [range_windowRow]; exact y.2
  obtain ⟨p, hp⟩ := hy
  have hsplit : y = p.1 • (⟨entireCenteredWindow 2, entireCenteredWindow_mem_xiIdeal 2⟩ :
        ↥deningerEntireXiIdeal)
      + p.2 • (⟨entireCenteredWindow 3, entireCenteredWindow_mem_xiIdeal 3⟩ :
        ↥deningerEntireXiIdeal) := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
    rw [← hp, windowRow_apply]
  rw [hsplit, map_add, map_smul, map_smul]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [windowCotangent])))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [windowCotangent])))


end HedenmalmThetaSource

end

end RHTower
