import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The orientation index of a cycle

The Hodge defect of a configuration counts its zeros right of the critical line, and the defect
already lives on the translates of one spectrally generic test (Arithmetic Castelnuovo–Severi,
`cyclic_pontryagin_law`). Which negative squares does the orbit of an *arbitrary* cycle carry?

The answer is the zeros it sees. A test `f` **sees** a zero `ρ` when its transform vanishes at
neither point `γ_ρ, γ̄_ρ` of the reflection pair.

* **The seen configuration** (`seenConfig`). The zeros seen by `f` form a configuration: seeing is
  invariant under reflection. It is tempered with `Z` (`temperedConfig_seenConfig`), and `f` is
  spectrally generic on it (`spectrallyGeneric_seenConfig`).
* **The orbit does not see the rest** (`W_translate_seenConfig`). On the orbit of `f` the Weil form of
  `Z` is the Weil form of the seen configuration: every summand at an unseen zero vanishes.
* **The orientation index** (`orientationIndex_law`). For every set of shifts dense in `[0, ∞)`,
  the negative index of the Weil Gram matrix of finitely many translates of `f` reaches `n` iff `f`
  sees at least `n` zeros right of the line. The orientation index of a cycle — the number of
  negative squares on its orbit — is the number of right zeros it sees (`ℕ∞`-valued). No
  functional-equation symmetry is needed.
* **For `ζ`** (`zeta_orientationIndex_law`): the negative index of the Weil Gram matrices of
  translates of a real test, computed from primes, Gamma factor and pole, is the number of zeros of
  `ζ` right of the line that the test sees. With the signature law of the scaling surface this
  is the signature of the orbit surface (`zeta_orbit_signature_law`): one positive square plus one
  for every seen right zero.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.HTGeometry (hermNegIndex hermPosIndex)

/-- `f` **sees** `ρ`: its transform vanishes at neither point of the reflection pair of `ρ`. -/
def Sees (f : ℝ → ℝ) (ρ : ℂ) : Prop :=
  paperFT (cx f) (gammaOf ρ) ≠ 0 ∧ paperFT (cx f) (conj (gammaOf ρ)) ≠ 0

theorem sees_reflect {f : ℝ → ℝ} {ρ : ℂ} (h : Sees f ρ) : Sees f (reflect ρ) := by
  rw [Sees, gammaOf_reflect, conj_conj]
  exact ⟨h.2, h.1⟩

/-- **The configuration of the zeros seen by `f`.** -/
def seenConfig (Z : ZeroConfig) (f : ℝ → ℝ) : ZeroConfig where
  carrier := {ρ ∈ Z.carrier | Sees f ρ}
  mult := Z.mult
  one_le_mult ρ hρ := Z.one_le_mult ρ hρ.1
  strip ρ hρ := Z.strip ρ hρ.1
  reflect_mem ρ hρ := ⟨Z.reflect_mem ρ hρ.1, sees_reflect hρ.2⟩
  mult_reflect ρ hρ := Z.mult_reflect ρ hρ.1
  finite_window T₁ T₂ := (Z.finite_window T₁ T₂).subset fun _ hρ => ⟨hρ.1.1, hρ.2⟩

theorem seenConfig_carrier_subset (Z : ZeroConfig) (f : ℝ → ℝ) :
    (seenConfig Z f).carrier ⊆ Z.carrier := fun _ h => h.1

theorem temperedConfig_seenConfig {Z : ZeroConfig} (hZ : TemperedConfig Z) (f : ℝ → ℝ) :
    TemperedConfig (seenConfig Z f) :=
  (hZ.comp_injective (Set.inclusion_injective (seenConfig_carrier_subset Z f))).congr fun _ => rfl

theorem spectrallyGeneric_seenConfig (Z : ZeroConfig) (f : ℝ → ℝ) :
    SpectrallyGeneric (seenConfig Z f) (cx f) := fun _ hρ => hρ.2.1

/-- The complex form of a ArithmeticCastelnuovoSeveri.translate of a real test. -/
theorem cx_scaleShift_eq_translate (t : ℝ) (f : ℝ → ℝ) : cx (scaleShift t f) = ArithmeticCastelnuovoSeveri.translate t (cx f) :=
  rfl

/-- The summand of two translates of `f` vanishes at every zero `f` does not see. -/
theorem Wsummand_translate_eq_zero {Z : ZeroConfig} {f : ℝ → ℝ} {ρ : ℂ} (h : ¬ Sees f ρ)
    (s t : ℝ) : Z.Wsummand (ArithmeticCastelnuovoSeveri.translate s (cx f)) (ArithmeticCastelnuovoSeveri.translate t (cx f)) ρ = 0 := by
  rw [← cx_scaleShift_eq_translate, ← cx_scaleShift_eq_translate, Wsummand_scaleShift]
  rw [Sees, not_and_or, not_not, not_not] at h
  rcases h with h | h
  · rw [ZeroConfig.Wsummand, h, mul_zero, zero_mul, mul_zero]
  · rw [ZeroConfig.Wsummand, h, map_zero, mul_zero, mul_zero]

/-- **On the orbit of `f`, the Weil form of `Z` is that of the zeros `f` sees.** -/
theorem W_translate_seenConfig (Z : ZeroConfig) (f : ℝ → ℝ) (s t : ℝ) :
    Z.W (ArithmeticCastelnuovoSeveri.translate s (cx f)) (ArithmeticCastelnuovoSeveri.translate t (cx f)) =
      (seenConfig Z f).W (ArithmeticCastelnuovoSeveri.translate s (cx f)) (ArithmeticCastelnuovoSeveri.translate t (cx f)) := by
  set F : ℂ → ℂ := fun ρ => Z.Wsummand (ArithmeticCastelnuovoSeveri.translate s (cx f)) (ArithmeticCastelnuovoSeveri.translate t (cx f)) ρ with hF
  have hW : (seenConfig Z f).W (ArithmeticCastelnuovoSeveri.translate s (cx f)) (ArithmeticCastelnuovoSeveri.translate t (cx f)) =
      ∑' ρ : (seenConfig Z f).carrier, F ρ := rfl
  rw [ZeroConfig.W, hW, _root_.tsum_subtype, _root_.tsum_subtype]
  congr 1
  funext ρ
  by_cases hρ : ρ ∈ Z.carrier
  · by_cases hs : Sees f ρ
    · rw [Set.indicator_of_mem hρ, Set.indicator_of_mem (show ρ ∈ (seenConfig Z f).carrier from ⟨hρ, hs⟩)]
    · rw [Set.indicator_of_mem hρ, Set.indicator_of_notMem (fun h => hs h.2),
        Wsummand_translate_eq_zero hs]
  · rw [Set.indicator_of_notMem hρ, Set.indicator_of_notMem (fun h => hρ h.1)]

theorem zeroGram_translates_seenConfig (Z : ZeroConfig) (f : ℝ → ℝ) (S : Finset ℝ) :
    zeroGram Z (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f)) =
      zeroGram (seenConfig Z f) (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f)) :=
  Matrix.ext fun i j => W_translate_seenConfig Z f i j

/-- The right zeros seen by `f`. -/
def seenRightZeros (Z : ZeroConfig) (f : ℝ → ℝ) : Set ℂ :=
  {ρ ∈ Z.carrier | 1 / 2 < ρ.re ∧ Sees f ρ}

theorem rightZeros_seenConfig (Z : ZeroConfig) (f : ℝ → ℝ) :
    rightZeros (seenConfig Z f) = seenRightZeros Z f := by
  ext ρ
  simp only [rightZeros, seenRightZeros, seenConfig, Set.mem_setOf_eq]
  tauto

/-- **The orientation index law.** For a real test `f ∈ C²_c` on a tempered configuration and shifts
`D` dense in `[0, ∞)`: some finite family of translates `f(· − s)`, `s ∈ D`, has a Weil Gram matrix
with at least `n` negative squares iff `f` sees at least `n` zeros right of the critical line. -/
theorem orientationIndex_law (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {D : Set ℝ} (hD : DenseShifts D) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ D ∧ n ≤ hermNegIndex (zeroGram Z fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f))) ↔
      (n : ℕ∞) ≤ (seenRightZeros Z f).encard := by
  have hcyc := cyclic_pontryagin_law (seenConfig Z f) (temperedConfig_seenConfig hZ f)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2) (spectrallyGeneric_seenConfig Z f) hD n
  rw [rightZeros_seenConfig] at hcyc
  refine (exists_congr fun S => and_congr_right fun _ => ?_).trans hcyc
  rw [zeroGram_translates_seenConfig Z f S]

/-- **An orbit with no negative square sees no right zero.** -/
theorem orientationIndex_eq_zero_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {D : Set ℝ} (hD : DenseShifts D) :
    (∀ S : Finset ℝ, ↑S ⊆ D → hermNegIndex (zeroGram Z fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f)) = 0) ↔
      seenRightZeros Z f = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (seenRightZeros Z f).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨ρ, hρ⟩
    obtain ⟨S, hS, hn⟩ := (orientationIndex_law Z hZ hf hD 1).mpr h1
    rw [h S hS] at hn
    exact absurd hn (by norm_num)
  · intro h S hS
    by_contra hne
    have h1 : 1 ≤ hermNegIndex (zeroGram Z fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f)) :=
      Nat.one_le_iff_ne_zero.mpr hne
    have := (orientationIndex_law Z hZ hf hD 1).mp ⟨S, hS, h1⟩
    rw [h, Set.encard_empty] at this
    exact absurd this (by norm_num)

/-- **For `ζ`**: the negative index of the Weil Gram matrices of translates of a real test, with
the Weil form computed from primes, Gamma factor and pole, is the number of zeros of `ζ` right of
the line that the test sees. -/
theorem zeta_orientationIndex_law {f : ℝ → ℝ} (hf : f ∈ realTests) {D : Set ℝ}
    (hD : DenseShifts D) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ D ∧ n ≤ hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f))) ↔
      (n : ℕ∞) ≤ (seenRightZeros zetaZeroConfig f).encard := by
  have hW : ∀ S : Finset ℝ, weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f)) = zeroGram zetaZeroConfig fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f) :=
    fun S => weilGram_eq_zeroGram _ (fun s => translate_contDiff (cx_contDiff hf.1) s)
      (fun s => translate_hasCompactSupport (cx_hasCompactSupport hf.2) s)
  refine (exists_congr fun S => and_congr_right fun _ => ?_).trans
    (orientationIndex_law zetaZeroConfig temperedConfig_zetaZeroConfig hf hD n)
  rw [hW S]

/-- **The signature of an orbit surface.** The intersection Gram matrix of the pole plane and finitely
many translates of a real test has at least `n + 1` positive squares, for some finite family of
shifts in `D`, iff the test sees at least `n` zeros of `ζ` right of the line: the orbit surface has
one positive square plus one for every seen right zero. -/
theorem zeta_orbit_signature_law {f : ℝ → ℝ} (hf : f ∈ realTests) {D : Set ℝ}
    (hD : DenseShifts D) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ D ∧ n + 1 ≤ hermPosIndex (intersectionGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx f))) ↔
      (n : ℕ∞) ≤ (seenRightZeros zetaZeroConfig f).encard := by
  have h : ∀ S : Finset ℝ, n + 1 ≤ hermPosIndex (intersectionGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx f)) ↔
      n ≤ hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx f)) := fun S => by
    rw [posIndex_intersectionGram]; omega
  exact (exists_congr fun S => and_congr_right fun _ => h S).trans
    (zeta_orientationIndex_law hf hD n)

end GaloisForLFunctions.ArithmeticOrientationGeometry
