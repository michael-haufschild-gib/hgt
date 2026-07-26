/-
# Explicit anisotropic grid for Bourgain's period cells

The sharp phase cell has coordinate half-widths
`H/2,H²/2,H/2,H²/2`.  This module constructs an exact half-open product
grid, proves its cardinality, and pulls the cover back through the combined
osculating phase equivalence.
-/
import GaloisForLFunctions.RHTower.BourgainAnisotropicFundamentalCell
import GaloisForLFunctions.RHTower.BourgainExplicitCubeGrid

namespace RHTower

noncomputable section

/-- Half-open one-dimensional grid cover, matching the `Ioc` convention of
Lebesgue product cells. -/
theorem exists_bourgainGridCenter1D_Ioc
    (m : ℕ) {r x : ℝ} (hr : 0 < r)
    (hx : x ∈ Set.Ioc
      (-((m + 1 : ℕ) : ℝ) * r)
      (((m + 1 : ℕ) : ℝ) * r)) :
    ∃ k : Fin (m + 1),
      x - bourgainGridCenter1D (m + 1) r k ∈ Set.Ioc (-r) r := by
  induction m generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      simpa [bourgainGridCenter1D] using hx
  | succ m ih =>
      have htotal :
          (((m + 1 + 1 : ℕ) : ℝ) * r) =
            ((m + 1 : ℕ) : ℝ) * r + r := by
        push_cast
        ring
      have htotalNeg :
          -(((m + 1 + 1 : ℕ) : ℝ) * r) =
            -(((m + 1 : ℕ) : ℝ) * r) - r := by
        rw [htotal]
        ring
      rw [htotal, htotalNeg] at hx
      by_cases hleft :
          x ≤ -((m + 1 : ℕ) : ℝ) * r + r
      · refine ⟨0, ?_⟩
        have hc0 :
            bourgainGridCenter1D (m + 1 + 1) r
                (0 : Fin (m + 1 + 1)) =
              -((m + 1 : ℕ) : ℝ) * r := by
          unfold bourgainGridCenter1D
          simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
          push_cast
          ring
        rw [hc0]
        constructor <;> linarith
      · have hxshift :
          x - r ∈ Set.Ioc
            (-((m + 1 : ℕ) : ℝ) * r)
            (((m + 1 : ℕ) : ℝ) * r) := by
          constructor
          · have hleft' := lt_of_not_ge hleft
            linarith
          · linarith
        obtain ⟨k, hk⟩ := ih hxshift
        refine ⟨Fin.succ k, ?_⟩
        have hcenter :
            bourgainGridCenter1D (m + 2) r (Fin.succ k) =
              bourgainGridCenter1D (m + 1) r k + r := by
          unfold bourgainGridCenter1D
          norm_num [Fin.val_succ]
          ring
        rw [hcenter]
        convert hk using 1 <;> ring

/-- A centered coordinate box with independently specified half-widths. -/
def bourgainAnisotropicBox
    (R : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  Set.univ.pi fun j : Fin 4 => Set.Ioc (-R j) (R j)

/-- Product-grid index for coordinate-dependent cell counts. -/
abbrev BourgainAnisotropicGridIndex
    (m : Fin 4 → ℕ) := ∀ j : Fin 4, Fin (m j + 1)

/-- Center of an anisotropic phase-space grid cell. -/
def bourgainAnisotropicPhaseGridCenter
    (H : ℕ) (m : Fin 4 → ℕ)
    (k : BourgainAnisotropicGridIndex m) : BourgainPhaseSpace :=
  fun j =>
    bourgainGridCenter1D (m j + 1)
      (bourgainParabolaFundamentalHalfWidth H j) (k j)

/-- Half-widths of the full phase box covered by the grid. -/
def bourgainAnisotropicGridRadius
    (H : ℕ) (m : Fin 4 → ℕ) : BourgainPhaseSpace :=
  fun j =>
    ((m j + 1 : ℕ) : ℝ) *
      bourgainParabolaFundamentalHalfWidth H j

/-- Translation of the centered physical period cell in phase coordinates. -/
def bourgainTranslatedParabolaFundamentalCell
    (H : ℕ) (y : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  (fun z => z + y) '' bourgainParabolaFundamentalCell H

/-- Exact product-grid cover of the enlarged anisotropic phase box. -/
theorem bourgainAnisotropicBox_subset_phaseGridCover
    {H : ℕ} (hH : 0 < H) (m : Fin 4 → ℕ) :
    bourgainAnisotropicBox (bourgainAnisotropicGridRadius H m) ⊆
      ⋃ k : BourgainAnisotropicGridIndex m,
        bourgainTranslatedParabolaFundamentalCell H
          (bourgainAnisotropicPhaseGridCenter H m k) := by
  intro z hz
  have hwidth :
      ∀ j, 0 < bourgainParabolaFundamentalHalfWidth H j := by
    intro j
    fin_cases j <;>
      simp [bourgainParabolaFundamentalHalfWidth, Matrix.cons_val] <;>
      positivity
  have hzcoord (j : Fin 4) :
      z j ∈ Set.Ioc
        (-(((m j + 1 : ℕ) : ℝ) *
          bourgainParabolaFundamentalHalfWidth H j))
        (((m j + 1 : ℕ) : ℝ) *
          bourgainParabolaFundamentalHalfWidth H j) := by
    exact hz j (Set.mem_univ j)
  choose k hk using fun j =>
    exists_bourgainGridCenter1D_Ioc
      (m j) (r := bourgainParabolaFundamentalHalfWidth H j)
        (x := z j) (hwidth j) (hzcoord j)
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  refine ⟨z - bourgainAnisotropicPhaseGridCenter H m k, ?_, by simp⟩
  intro j hj
  simpa [bourgainParabolaFundamentalCell, bourgainFullBox,
    bourgainAnisotropicPhaseGridCenter] using hk j

/-- Exact number of anisotropic grid cells. -/
theorem card_bourgainAnisotropicGridIndex
    (m : Fin 4 → ℕ) :
    Fintype.card (BourgainAnisotropicGridIndex m) =
      ∏ j : Fin 4, (m j + 1) := by
  simp

/-- Combined osculating coordinate map as a continuous linear equivalence. -/
noncomputable def bourgainScaledOsculatingPhaseContinuousLinearEquiv
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    BourgainPhaseSpace ≃L[ℝ] BourgainPhaseSpace :=
  (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha hab).trans
    (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale)

@[simp] theorem bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) (x : BourgainPhaseSpace) :
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab x =
      bourgainScaledOsculatingPhaseCoordinates scale a b x := by
  simp [bourgainScaledOsculatingPhaseContinuousLinearEquiv,
    bourgainScaledOsculatingPhaseCoordinates,
    bourgainSquareRootPhaseCoordinateContinuousLinearEquiv_apply,
    bourgainParabolaPhaseScaleContinuousLinearEquiv_apply]

/-- Pullback center corresponding to a phase-grid center. -/
def bourgainOsculatingGridCenter
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b)
    (H : ℕ) (m : Fin 4 → ℕ)
    (k : BourgainAnisotropicGridIndex m) : BourgainPhaseSpace :=
  (bourgainScaledOsculatingPhaseContinuousLinearEquiv
    hscale ha hab).symm
      (bourgainAnisotropicPhaseGridCenter H m k)

/-- Pulling back the explicit phase grid gives a translated osculating-cell
cover with the same exact cardinality. -/
theorem preimage_bourgainAnisotropicBox_subset_osculatingGridCover
    {H : ℕ} (hH : 0 < H) (m : Fin 4 → ℕ)
    {scale a b : ℝ} (hscale : scale ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    bourgainScaledOsculatingPhaseCoordinates scale a b ⁻¹'
        bourgainAnisotropicBox
          (bourgainAnisotropicGridRadius H m) ⊆
      ⋃ k : BourgainAnisotropicGridIndex m,
        bourgainTranslatedOsculatingFundamentalCell
          H scale a b
            (bourgainOsculatingGridCenter
              hscale ha hab H m k) := by
  intro x hx
  have hphase :=
    bourgainAnisotropicBox_subset_phaseGridCover hH m hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hphase
  apply Set.mem_iUnion.2
  refine ⟨k, ?_⟩
  obtain ⟨w, hw, hwy⟩ := hk
  let e :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab
  let c := bourgainAnisotropicPhaseGridCenter H m k
  let y := bourgainOsculatingGridCenter hscale ha hab H m k
  refine ⟨x - y, ?_, ?_⟩
  · change
      bourgainScaledOsculatingPhaseCoordinates scale a b (x - y) ∈
        bourgainParabolaFundamentalCell H
    have hey : e y = c := by
      dsimp [e, y, c, bourgainOsculatingGridCenter]
      rw [ContinuousLinearEquiv.apply_symm_apply]
    have hex : e x =
        bourgainScaledOsculatingPhaseCoordinates scale a b x :=
      bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
        hscale ha hab x
    have hwy' : w + c = e x := by
      simpa [c, hex] using hwy
    have hdiff : e (x - y) = w := by
      rw [map_sub, hey]
      exact sub_eq_of_eq_add hwy'.symm
    rw [← bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
      hscale ha hab]
    rw [hdiff]
    exact hw
  · simpa [y] using sub_add_cancel x y

end

end RHTower
