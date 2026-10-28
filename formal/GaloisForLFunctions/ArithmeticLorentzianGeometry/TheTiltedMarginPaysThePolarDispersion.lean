import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.ArithmeticLorentzianGeometry.PolarGluingAndDispersion

/-!
# The tilted margin pays the polar dispersion

A decomposition of `ζ`'s atomic intersection form into source-defined local pieces, glued at the
anchor `e = H + V`, with an exactly identified negative semidefinite residual.

* **Atom pieces** (`atomPiece`): the piece at the atom `m` carries the share `J/N` of the pole
  plane, the pole couplings `(∫ g_m e^{−u/2}, ∫ g_m e^{u/2})` of that atom, and its tilted margin
  `−‖g‖²μ_m` (`atomMargin`). The pieces sum to the **tilted diagonal model**
  (`sum_atomPiece`), and each has `Q_m[e] = 2/N`.
* **The exact decomposition** (`atomicIntersectionGram_eq_tiltedModel_add`): the atomic
  intersection form is the tilted diagonal model plus the residual `‖g‖² diag(μ) − M`, which is
  negative semidefinite at `w ≤ δ_N/2` by the row-by-row stability law (`qf_residual_nonpos`).
* **The dispersion is paid** (`polarDispersion_le_sum_anchorReserve`): at `w ≤ c★δ_N` the tilted
  model has one positive square, so by the polar gluing law the dispersion of the local polar rows
  about the global one is at most the sum of the local reserves.

This answers the polar-compatibility question of the programme in the stability regime: the
archimedean self-energy, distributed over the atoms by the tilt of the prime rows, pays the polar
dispersion of the atom pieces; the residual is a negative semidefinite correction proved by the
stability law. The construction is twist-blind, as the stability regime is.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The atom pieces and the tilted model -/

/-- The tilted margins of the atoms `1, …, N` scaled by `‖g‖²`. -/
def tiltedMargins (g : ℝ → ℝ) (w : ℝ) (N : ℕ) : Fin N → ℝ :=
  fun j => (∫ u, g u ^ 2) * atomMargin w N ((j : ℕ) + 1)

/-- The **tilted diagonal model**: pole plane, pole row of the atoms, block `−‖g‖² diag(μ)`. -/
def tiltedModel (g : ℝ → ℝ) (w : ℝ) (N : ℕ) : Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  fromBlocks realPolePlane (atomPoleRow g N) (atomPoleRow g N)ᵀ (-diagonal (tiltedMargins g w N))

/-- The **atom piece** at `m`: the share `J/N` of the pole plane, the pole couplings of `g_m` and
its tilted margin. -/
def atomPiece (g : ℝ → ℝ) (w : ℝ) (N : ℕ) (m : Fin N) :
    Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  fromBlocks ((N : ℝ)⁻¹ • realPolePlane)
    (Matrix.of fun a j => if j = m then atomPoleRow g N a j else 0)
    (Matrix.of fun j a => if j = m then atomPoleRow g N a j else 0)
    (Matrix.of fun i j => if i = m ∧ j = m then -tiltedMargins g w N m else 0)

theorem atomPiece_isSymm (g : ℝ → ℝ) (w : ℝ) (N : ℕ) (m : Fin N) :
    (atomPiece g w N m).IsSymm := by
  unfold atomPiece Matrix.IsSymm
  rw [fromBlocks_transpose]
  congr 1
  · ext a b; fin_cases a <;> fin_cases b <;> simp [realPolePlane]
  · ext i j; simp only [transpose_apply, Matrix.of_apply]; split_ifs <;> simp_all

/-- **The pieces sum to the tilted model.** -/
theorem sum_atomPiece (g : ℝ → ℝ) (w : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m, atomPiece g w N m = tiltedModel g w N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  ext i j
  rw [Matrix.sum_apply]
  rcases i with a | i <;> rcases j with b | j
  · simp only [atomPiece, tiltedModel, fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · simp only [atomPiece, tiltedModel, fromBlocks_apply₁₂, Matrix.of_apply]
    rw [Finset.sum_ite_eq]; simp
  · simp only [atomPiece, tiltedModel, fromBlocks_apply₂₁, Matrix.of_apply, transpose_apply]
    rw [Finset.sum_ite_eq]; simp
  · simp only [atomPiece, tiltedModel, fromBlocks_apply₂₂, Matrix.of_apply, Matrix.neg_apply,
      diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, neg_zero]
      exact sum_eq_zero fun x _ => if_neg fun h => hij (h.1.trans h.2.symm)

/-- The anchor `e = H + V`. -/
def poleAnchor (N : ℕ) : Fin 2 ⊕ Fin N → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

theorem qf_atomPiece_poleAnchor (g : ℝ → ℝ) (w : ℝ) {N : ℕ} (m : Fin N) :
    qf (atomPiece g w N m) (poleAnchor N) = 2 / N := by
  simp only [qf_eq_sum, Fintype.sum_sum_type, poleAnchor, Sum.elim_inl, Sum.elim_inr, atomPiece,
    fromBlocks_apply₁₁, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, realPolePlane, mul_zero, zero_mul, sum_const_zero, add_zero]
  simp
  ring

/-! ### The exact decomposition -/

/-- The residual `‖g‖² diag(μ) − M` of the decomposition. -/
def tiltedResidual (g : ℝ → ℝ) (w : ℝ) (N : ℕ) : Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  fromBlocks 0 0 0 (diagonal (tiltedMargins g w N) - atomicMarkovGram g N)

/-- **The exact decomposition**: atomic intersection form = tilted model + residual. -/
theorem atomicIntersectionGram_eq_tiltedModel_add (g : ℝ → ℝ) (w : ℝ) (N : ℕ) :
    atomicIntersectionGram g N = tiltedModel g w N + tiltedResidual g w N := by
  unfold atomicIntersectionGram tiltedModel tiltedResidual
  rw [fromBlocks_add]
  congr 1 <;> try simp
  ext i j
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.sub_apply, diagonal_apply]
  split_ifs <;> ring

/-- **The residual is negative semidefinite** at `w ≤ δ_N/2`: the row-by-row stability law. -/
theorem qf_residual_nonpos (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) (v : Fin 2 ⊕ Fin N → ℝ) :
    qf (tiltedResidual g w N) v ≤ 0 := by
  set d : Fin N → ℝ := v ∘ Sum.inr
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  -- the quadratic form only sees the atom coordinates
  have hq : qf (tiltedResidual g w N) v =
      ∑ j, tiltedMargins g w N j * d j ^ 2 - levyMarkovForm (finAtomicTest g N d) := by
    have hM : qf (atomicMarkovGram g N) d = levyMarkovForm (finAtomicTest g N d) := by
      rw [show finAtomicTest g N d = fun u => ∑ j, d j * atom g ((j : ℕ) + 1) u from rfl,
        levyMarkovForm_sum_eq _ (fun j => contDiff_atom hg _)
          (fun j => hasCompactSupport_atom hgsupp _)
          (fun j => supportedIn_atom hgsupp hw0.le (mem_Icc_succ j)), qf_eq_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      simp only [atomicMarkovGram, Matrix.of_apply]; ring
    have hD : qf (diagonal (tiltedMargins g w N)) d = ∑ j, tiltedMargins g w N j * d j ^ 2 := by
      rw [qf_eq_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_eq_single i (fun j _ hji => by simp [Ne.symm hji]) (by simp)]
      simp; ring
    rw [← hM, ← hD, ← qf_sub_matrix]
    simp only [qf_eq_sum, Fintype.sum_sum_type, tiltedResidual, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
      zero_mul, sum_const_zero, zero_add, add_zero, d, Function.comp_apply]
  rw [hq, finAtomicTest_eq_atomicTest]
  set x : ℕ → ℝ := fun n => if h : 1 ≤ n ∧ n ≤ N then d ⟨n - 1, by omega⟩ else 0
  have h := atomMargin_mul_le_levy_sub hg hgc hgsupp hN hw0 hw x x fun _ _ => rfl
  rw [← primeSum_atomicTest hg hgc hgsupp hwδ x] at h
  have hsum : (∫ u, g u ^ 2) * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m =
      ∑ j, tiltedMargins g w N j * d j ^ 2 := by
    rw [sum_Icc_one_eq_sum_fin, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [x, tiltedMargins, dif_pos (show 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ N by omega),
      Nat.add_sub_cancel, Fin.eta]
    ring
  unfold levyMarkovForm
  linarith

/-! ### The dispersion is paid -/

/-- **The tilted model has one positive square** at `w ≤ c★δ_N`. -/
theorem tiltedModel_isHyperbolic (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) : IsHyperbolic (tiltedModel g w N) := by
  have hL : (-diagonal (tiltedMargins g w N)).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_neg, diagonal_transpose]
  rw [tiltedModel, isHyperbolic_fromBlocks_iff _ hL]
  intro d
  set f := finAtomicTest g N d
  have hB0 : (atomPoleRow g N *ᵥ d) 0 = ∫ u, f u * Real.exp (-(u / 2)) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (-(u / 2))) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, if_true]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hB1 : (atomPoleRow g N *ᵥ d) 1 = ∫ u, f u * Real.exp (u / 2) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (u / 2)) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hD : qf (-diagonal (tiltedMargins g w N)) d = -∑ j, tiltedMargins g w N j * d j ^ 2 := by
    rw [qf_eq_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i (fun j _ hji => by simp [Ne.symm hji]) (by simp)]
    simp; ring
  rw [polarDefect, hB0, hB1, hD]
  set x : ℕ → ℝ := fun n => if h : 1 ≤ n ∧ n ≤ N then d ⟨n - 1, by omega⟩ else 0
  have hfx : f = atomicTest N x g := finAtomicTest_eq_atomicTest g N d
  have hpole := two_mul_abs_poleMoments_le_margin hg hgc hgsupp hN hw0 hw x
  have hsum : (∫ u, g u ^ 2) * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m =
      ∑ j, tiltedMargins g w N j * d j ^ 2 := by
    rw [sum_Icc_one_eq_sum_fin, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [x, tiltedMargins, dif_pos (show 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ N by omega),
      Nat.add_sub_cancel, Fin.eta]
    ring
  rw [hfx]
  have := neg_abs_le ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
    ∫ u, atomicTest N x g u * Real.exp (u / 2))
  nlinarith

/-- **The tilted margin pays the polar dispersion.** At `w ≤ c★δ_N`, the dispersion of the polar
rows of the atom pieces about the global one, at the anchor `H + V`, is at most the sum of their
local reserves. -/
theorem polarDispersion_le_sum_anchorReserve (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) (x : Fin 2 ⊕ Fin N → ℝ) :
    polarDispersion (atomPiece g w N) (poleAnchor N) x ≤
      ∑ m, anchorReserve (atomPiece g w N m) (poleAnchor N) x := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : ∀ m, 0 < qf (atomPiece g w N m) (poleAnchor N) := fun m => by
    rw [qf_atomPiece_poleAnchor]; positivity
  have hsum : IsHyperbolic (∑ m, atomPiece g w N m) := by
    rw [sum_atomPiece g w hN]
    exact tiltedModel_isHyperbolic hg hgc hgsupp hN hw0 hw
  exact (isHyperbolic_sum_iff_dispersion_le (atomPiece g w N) (atomPiece_isSymm g w N)
    (poleAnchor N) he).mp hsum x

end GaloisForLFunctions.ArithmeticLorentzianGeometry
