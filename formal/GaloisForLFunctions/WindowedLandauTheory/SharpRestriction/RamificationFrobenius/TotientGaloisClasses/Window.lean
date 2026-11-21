import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import GaloisForLFunctions.WindowedLandauTheory.WindowedCesaroBoundsForceZeroFreeHalfPlanes

/-! Multiplicative windows and the level form of the Landau criterion. -/

noncomputable section

namespace WindowedLandauTheory.HC

def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S

theorem HasWindows.mono {S S' : Set ℝ} {la x0 : ℝ} (h : HasWindows S la) (hS : ∀ x ≥ x0, x ∈ S → x ∈ S') :
    HasWindows S' la := by
  intro y
  obtain ⟨Y, hyY, hY⟩ := h (max y x0)
  exact ⟨Y, (le_max_left _ _).trans hyY,
    fun x h1 h2 => hS x ((le_max_right _ _).trans (hyY.trans h1)) (hY x h1 h2)⟩

theorem hasWindows_of_large {S : Set ℝ} {x0 : ℝ} (h : ∀ x ≥ x0, x ∈ S) (la : ℝ) : HasWindows S la :=
  fun y => ⟨max y x0, le_max_left _ _, fun x h1 _ => h x ((le_max_right _ _).trans h1)⟩

namespace Level

variable (Λ : Level)

def LandauWinAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → (∃ ψ ∈ Λ.KEPT, ∃ s : ℂ, θ < s.re ∧ DirichletCharacter.LFunction ψ.χ s = 0) →
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∃ y : ℝ, Y ≤ y ∧ y ≤ Y ^ la ∧ y ^ θ < Λ.Gm y

def LandauWin : Prop := ∀ la : ℝ, 1 < la → Λ.LandauWinAt la

def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ

def FormB : Prop := ∀ la : ℝ, 1 < la → Λ.FormBAt la

variable {Λ}

theorem FormBAt.mono {la la' : ℝ} (h : Λ.FormBAt la) (hl : la ≤ la') : Λ.FormBAt la' := by
  unfold FormBAt at h ⊢
  intro θ h0 h1 hw
  apply h θ h0 h1
  intro y
  obtain ⟨Y, hyY, hY⟩ := hw (max y 1)
  refine ⟨Y, (le_max_left _ _).trans hyY, fun x hx1 hx2 => hY x hx1 (hx2.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hyY) hl

private theorem nonprincipal_cesaro_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (y : ℝ) : An.gChi χ y = charCesaroFunctional χ y := by
  simp only [An.gChi, if_neg hχ, charCesaroFunctional, An.logDerivativeAtOne, logDeriv]
  congr 1
  unfold An.sumLamChi cesaroRamp twistedVonMangoldt
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
  have hy : 0 ≤ y := zero_le_one.trans (Nat.floor_pos.mp (Nat.zero_lt_one.trans_le (hn₁.trans hn₂)))
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn₂).trans (Nat.floor_le hy)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn₁)
  have hramp : 0 ≤ y / (n : ℝ) - 1 :=
    sub_nonneg.mpr ((le_div_iff₀ hn₀).mpr (by simpa only [one_mul] using hny))
  rw [max_eq_left hramp, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, mul_comm (An.abelian₂ n : ℂ)]

/-- The windowed Landau criterion applied to the nonprincipal members of a level,
with the zeta term accounting for the principal member. -/
theorem formB (Λ : Level) : Λ.FormB := by
  classical
  intro la hla θ hθ _ hwin ψ hψ s hs
  let ι := ↥Λ.Nt
  let χ (i : ι) : DirichletCharacter ℂ i.val.N := i.val.χ
  letI : ∀ i : ι, NeZero i.val.N := fun i => i.val.ne
  have hχ (i : ι) : χ i ≠ 1 := by
    intro hi
    have he := (PChar.of_self i.val).symm
    rw [show i.val.χ = 1 from hi, PChar.of_one] at he
    exact (Finset.mem_erase.mp i.property).1 he
  have hweight (i : ι) : 0 < Λ.wt i.val := by
    unfold wt
    split <;> positivity
  have hfunctional (y : ℝ) : Λ.Gm y = familyCesaroFunctional χ (fun i => Λ.wt i.val) y := by
    have hz : Gz y = zetaCesaroFunctional y := rfl
    rw [Gm, familyCesaroFunctional, hz, ← Finset.sum_coe_sort Λ.Nt]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [nonprincipal_cesaro_eq _ (hχ i)]
  have hexponent : 1 + (la - 1) = la := by ring
  have hb : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Set.Icc Y (Y ^ (1 + (la - 1))),
      familyCesaroFunctional χ (fun i => Λ.wt i.val) y ≤ 1 * y ^ θ := by
    intro Y₀
    obtain ⟨Y, hY, hbound⟩ := hwin Y₀
    refine ⟨Y, hY, fun y hy => ?_⟩
    rw [hexponent] at hy
    have hlevel : Λ.Gm y ≤ y ^ θ := hbound y hy.1 hy.2
    simpa only [← hfunctional, one_mul] using hlevel
  obtain ⟨hz, hmembers⟩ := zeroFree_of_windowed_cesaro_bound hχ (fun i => Λ.wt i.val)
    hweight hθ.le (sub_pos.mpr hla) hb s hs
  by_cases hprincipal : ψ = PChar.one
  · subst ψ
    change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0
    rwa [DirichletCharacter.LFunction_modOne_eq]
  · exact hmembers ⟨ψ, Finset.mem_erase.mpr ⟨hprincipal, hψ⟩⟩

end Level

end WindowedLandauTheory.HC

end
