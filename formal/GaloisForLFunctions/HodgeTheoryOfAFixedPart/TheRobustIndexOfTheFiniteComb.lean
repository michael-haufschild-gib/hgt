import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.BoundedPacketIndexCountsNoExtraZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets

/-!
# Negative squares of the finite comb with a fixed margin

The complex form is the sum of the real forms of the two components.
Its robust negative index counts subspaces below a fixed negative multiple
of coefficient mass. Linear transfer to a finite packet Gram bounds this
index once every negative direction has been transferred.
-/

noncomputable section

open Finset Matrix Filter Topology

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ

/-- Polarization of nested windows is the elementary three-window entry
used by the finite-scale comb limit. -/
theorem packetFormGram_nested_eq_stepEntry {n Q x₀ X : ℕ}
    (hx₀ : 1 ≤ x₀) (x : Fin n → ℕ) (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X)
    (i j : Fin n) :
    packetFormGram Q (fun k => flatPacket x₀ (x k)) i j =
      ((stepEntry Q x₀ x i j / 2 : ℝ) : ℂ) := by
  have hxx : ∀ k ∈ (univ : Finset (Fin 2)),
      x₀ ≤ (![x i, x j] : Fin 2 → ℕ) k ∧ (![x i, x j] : Fin 2 → ℕ) k ≤ X := by
    intro k _
    fin_cases k
    · exact hx i
    · exact hx j
  have hzero (a : ℕ) : packetForm Q (flatPacket (a : ℝ) a) = 0 := by
    simp [flatPacket, packetForm, packetAutocorr, levyJump]
  have hp := packetForm_nested_eq (Q := Q) hx₀ hxx (fun _ : Fin 2 => (1 : ℝ))
  have hm := packetForm_nested_eq (Q := Q) hx₀ hxx (![1, -1] : Fin 2 → ℝ)
  simp [Fin.sum_univ_two, stepEntry, hzero, min_comm, max_comm] at hp hm
  simp only [← sub_eq_add_neg] at hm
  change packetForm Q (flatPacket x₀ (x i) + flatPacket x₀ (x j)) = _ at hp
  change packetForm Q (flatPacket x₀ (x i) - flatPacket x₀ (x j)) = _ at hm
  unfold packetFormGram
  apply congrArg Complex.ofReal
  dsimp only [stepEntry]
  simp only [Nat.cast_min, Nat.cast_max]
  nlinarith only [hp, hm]

/-- The nested-window Gram represents the full real and imaginary packet
forms, so its index applies to complex block coefficients as well. -/
theorem hermQuad_packetFormGram_nested {n Q x₀ X : ℕ}
    (hx₀ : 1 ≤ x₀) (x : Fin n → ℕ) (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X)
    (c : Fin n → ℂ) :
    hermQuad (packetFormGram Q (fun i => flatPacket x₀ (x i))) c =
      packetForm Q (fun u => ∑ i, (c i).re * flatPacket x₀ (x i) u) +
        packetForm Q (fun u => ∑ i, (c i).im * flatPacket x₀ (x i) u) := by
  have hmat : packetFormGram Q (fun i => flatPacket x₀ (x i)) =
      fun i j => ((stepEntry Q x₀ x i j / 2 : ℝ) : ℂ) := by
    ext i j
    exact packetFormGram_nested_eq_stepEntry hx₀ x hx i j
  rw [hmat, packetForm_nested_eq hx₀ (fun i _ => hx i),
    packetForm_nested_eq hx₀ (fun i _ => hx i)]
  simp only [hermQuad, dotProduct, mulVec, Finset.mul_sum, Complex.re_sum,
    Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_add, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Extend coefficients on a finite set of degree points by zero. -/
def combExtension (S : Finset ℕ) : (S → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun c n := if h : n ∈ S then c ⟨n, h⟩ else 0
  map_add' c d := by ext n; by_cases hn : n ∈ S <;> simp [hn]
  map_smul' a c := by ext n; by_cases hn : n ∈ S <;> simp [hn]

/-- The Hermitian extension of the literal real comb form. -/
def complexCombForm (S : Finset ℕ) (c : S → ℂ) : ℝ :=
  combForm S (fun n => (combExtension S c n).re) +
    combForm S (fun n => (combExtension S c n).im)

theorem combExtension_mass (S : Finset ℕ) (c : S → ℂ) :
    (∑ n ∈ S, (combExtension S c n).re ^ 2) +
        (∑ n ∈ S, (combExtension S c n).im ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  have hnorm : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [hnorm]
  simpa [combExtension] using (Finset.sum_attach S (fun n => ‖combExtension S c n‖ ^ 2)).symm

/-- Negative directions separated from zero by the fixed mass margin `η`. -/
def robustCombIndex (S : Finset ℕ) (η : ℝ) : ℕ∞ :=
  ⨆ (W : Submodule ℂ (S → ℂ))
    (_ : ∀ c ∈ W, c ≠ 0 → complexCombForm S c + η * ∑ i, ‖c i‖ ^ 2 < 0),
    (Module.finrank ℂ W : ℕ∞)

/-- A linear map carrying all robust negative directions to a fixed Gram
is injective on every negative subspace and bounds the full robust index. -/
theorem robustCombIndex_le_of_linear_transfer {S : Finset ℕ} {η : ℝ} {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (B : (S → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hB : ∀ c, complexCombForm S c + η * ∑ i, ‖c i‖ ^ 2 < 0 →
      hermQuad H (B c) < 0) :
    robustCombIndex S η ≤ (hermNegIndex H : ℕ∞) := by
  refine iSup_le fun W => iSup_le fun hW => ?_
  let L : W →ₗ[ℂ] (Fin n → ℂ) := B.comp W.subtype
  have hLinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hval : ((x - y : W) : S → ℂ) ≠ 0 := fun hz => hne (Subtype.ext hz)
    have hn := hB (x - y) (hW (x - y) (x - y).property hval)
    have heq : B ((x : S → ℂ) - (y : S → ℂ)) = 0 := by
      change L (x - y) = 0
      rw [map_sub, hxy, sub_self]
    rw [heq] at hn
    simpa only [hermQuad, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re,
      lt_self_iff_false] using hn
  have hpos : IsPosDefOn (-H) (LinearMap.range L) := by
    rintro _ ⟨c, rfl⟩ hc
    have hc0 : (c : S → ℂ) ≠ 0 := by
      intro hz
      apply hc
      have hc' : c = 0 := Subtype.ext hz
      rw [hc', map_zero]
    rw [hermQuad_neg]
    exact neg_pos.mpr (hB c (hW c c.property hc0))
  have hdim := finrank_le_posIndex hpos
  rw [LinearMap.finrank_range_of_inj hLinj] at hdim
  exact ENat.coe_le_coe.mpr hdim

/-- A finite Gram realized by the shifted comb form contributes all its
negative squares. Its realizing map is automatically injective on a
negative subspace. -/
theorem hermNegIndex_le_robustCombIndex {S : Finset ℕ} {η : ℝ} {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (A : (Fin n → ℂ) →ₗ[ℂ] (S → ℂ))
    (hA : ∀ c, complexCombForm S (A c) + η * ∑ i, ‖A c i‖ ^ 2 = hermQuad H c) :
    (hermNegIndex H : ℕ∞) ≤ robustCombIndex S η := by
  obtain ⟨W, hdim, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  let L := A.comp W.subtype
  have hn (c : W) (hc : c ≠ 0) : hermQuad H c < 0 := by
    have hc' : (c : Fin n → ℂ) ≠ 0 := fun hz => hc (Subtype.ext hz)
    have h := hW c c.property hc'
    rw [hermQuad_neg] at h
    exact neg_pos.mp h
  have hLinj : Function.Injective L := by
    intro c d hcd
    apply sub_eq_zero.mp
    by_contra hne
    have h := hn (c - d) hne
    rw [← hA] at h
    have hz : A ((c - d : W) : Fin n → ℂ) = 0 := by
      change L (c - d) = 0
      rw [map_sub, hcd, sub_self]
    rw [hz] at h
    simpa [complexCombForm, combExtension, combForm, combPairing, degOne, degTwo] using h
  have hrange : ∀ c ∈ LinearMap.range L, c ≠ 0 →
      complexCombForm S c + η * ∑ i, ‖c i‖ ^ 2 < 0 := by
    rintro _ ⟨c, rfl⟩ hc
    rw [show L c = A c from rfl, hA]
    exact hn c (fun hz => hc (by rw [hz, map_zero]))
  have hb : (Module.finrank ℂ (LinearMap.range L) : ℕ∞) ≤ robustCombIndex S η :=
    le_iSup_of_le (LinearMap.range L) (le_iSup_of_le hrange le_rfl)
  rwa [LinearMap.finrank_range_of_inj hLinj, hdim] at hb

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
