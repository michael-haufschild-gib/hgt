import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsWeighsTheZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm

/-!
# The Hodge index of the pairing of the degree points

For a finite family of packets `f₁, …, f_r` in one window and real coefficients `x`, the pairing
of the degree points on the combination `f_x = Σ x_i f_i` has the limit `2 d₁ d₂ − Z(f_x)`. Both
terms are quadratic forms in `x`, and the index law of the scaling surface (corpus) reads on the
degree points.

* **The local block** (`tendsto_degreePairing_packetCombination`, `hermQuad_localGram_packets`):
  the limit of jets, contacts and counterterm on `f_x` is the quadratic form at `x` of the local
  Gram matrix of the packets, the pole part `2 d₁(f_x) d₂(f_x)` minus Weil's Gram matrix. The
  Gram matrix of the cycles `H, V, f₁, …, f_r`, with the pole plane on `H, V`, the degrees in the
  mixed block and the finite part of the pairing of the degree points on the packets, is the
  arithmetic intersection form.
* **The index law** (`negIndex_defect_packets_le`, `posIndex_intersectionGram_packets_le`): the
  defect `2 d₁ d₂ − D·D` has at most as many negative squares on the family as `ζ` has zeros to
  the right of the critical line, and the intersection form has at most one more positive
  square than that.
* **The Hodge index theorem** (`riemannHypothesis_iff_one_positive_square_packets`): the
  Riemann hypothesis holds iff the intersection form has exactly one positive square on every
  finite family of packets.

So the inequality of Castelnuovo and Severi on the degree points can fail only on a space of
packets of dimension at most the number of zeros to the right of the line.
-/

open Finset Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {ι : Type*} [Fintype ι]

/-- The combination `Σ_i x_i f_i` of a family of packets. -/
def packetCombination (f : ι → ℝ → ℝ) (x : ι → ℝ) : ℝ → ℝ := fun u => ∑ i, x i * f i u

theorem contDiff_packetCombination {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (x : ι → ℝ) : ContDiff ℝ 2 (packetCombination f x) :=
  ContDiff.sum fun i _ => contDiff_const.mul (hf i)

theorem hasCompactSupport_packetCombination {f : ι → ℝ → ℝ}
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    HasCompactSupport (packetCombination f x) := by
  refine HasCompactSupport.intro (isCompact_iUnion fun i => hfc i) fun u hu => ?_
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [image_eq_zero_of_notMem_tsupport fun h => hu (Set.mem_iUnion.mpr ⟨i, h⟩), mul_zero]

theorem ofReal_packetCombination (f : ι → ℝ → ℝ) (x : ι → ℝ) :
    (fun u => ((packetCombination f x u : ℝ) : ℂ)) =
      ∑ i, conj ((x i : ℝ) : ℂ) • fun u => ((f i u : ℝ) : ℂ) := by
  funext u
  simp [packetCombination, Complex.conj_ofReal]

/-- The sum over the zeros of a combination of packets is the quadratic form of Weil's Gram
matrix of the family. -/
theorem zeroSum_packetCombination {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    zeroSum (packetCombination f x) =
      hermQuad (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
        fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)) := by
  rw [ArithmeticCastelnuovoSeveri.hermQuad_weilGram _ _
      (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i)),
    zeroSum_eq_weilFullFunctional (contDiff_packetCombination hf x)
      (hasCompactSupport_packetCombination hfc x), ofReal_packetCombination]

/-- **The pairing of the degree points on a combination of packets**: twice the product of the
degrees minus the quadratic form of Weil's Gram matrix. -/
theorem tendsto_degreePairing_packetCombination {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f i u = 0) (x : ι → ℝ) :
    Tendsto (fun N : ℕ => degreeForm (packetCombination f x) (3 * K) N +
        2 * degreeContact (packetCombination f x) (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, packetCombination f x u * Real.exp (-u / 2)) *
            ∫ u, packetCombination f x u * Real.exp (u / 2)) -
          hermQuad (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
            fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)))) := by
  have hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → packetCombination f x u = 0 := fun u hu =>
    Finset.sum_eq_zero fun i _ => by rw [hsupp i u hu, mul_zero]
  have h := tendsto_degreePairing_degrees_sub_zeroSum (contDiff_packetCombination hf x)
    (hasCompactSupport_packetCombination hfc x) hK hs
  rwa [zeroSum_packetCombination hf hfc x] at h

/-! ### The local block of the intersection form -/

/-- The quadratic form of the pole plane. -/
theorem hermQuad_polePlane (v : Fin 2 → ℂ) :
    hermQuad ArithmeticCastelnuovoSeveri.polePlane v = 2 * (conj (v 0) * v 1).re := by
  simp only [hermQuad, ArithmeticCastelnuovoSeveri.polePlane, dotProduct, mulVec,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [zero_mul, one_mul, zero_add, add_zero, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The pole row of a family of packets on a real vector: the two degrees of the combination. -/
theorem poleRow_mulVec_packets {f : ι → ℝ → ℝ} (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    (ArithmeticCastelnuovoSeveri.poleRow (fun i u => ((f i u : ℝ) : ℂ)) *ᵥ
        fun i => ((x i : ℝ) : ℂ)) 0 =
        ((∫ u, packetCombination f x u * Real.exp (-u / 2) : ℝ) : ℂ) ∧
      (ArithmeticCastelnuovoSeveri.poleRow (fun i u => ((f i u : ℝ) : ℂ)) *ᵥ
        fun i => ((x i : ℝ) : ℂ)) 1 =
        ((∫ u, packetCombination f x u * Real.exp (u / 2) : ℝ) : ℂ) := by
  have hint : ∀ (s : ℝ) (i : ι), Integrable fun u => x i * f i u * Real.exp (s * u) := fun s i =>
    ((continuous_const.mul (hf i)).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      ((hfc i).mul_left.mul_right)
  have hsum : ∀ s : ℝ, ∫ u, packetCombination f x u * Real.exp (s * u) =
      ∑ i, x i * ∫ u, f i u * Real.exp (s * u) := by
    intro s
    have e : (fun u => packetCombination f x u * Real.exp (s * u)) =
        fun u => ∑ i, x i * f i u * Real.exp (s * u) := by
      funext u
      rw [packetCombination, Finset.sum_mul]
    rw [e, integral_finset_sum _ fun i _ => hint s i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have e1 : ∀ u : ℝ, Real.exp (-u / 2) = Real.exp (-(1 / 2) * u) := fun u => by
    congr 1
    ring
  have e2 : ∀ u : ℝ, Real.exp (u / 2) = Real.exp (1 / 2 * u) := fun u => by
    congr 1
    ring
  have hneg : -(Complex.I / 2) = -Complex.I / 2 := by ring
  constructor
  · simp only [mulVec, dotProduct, ArithmeticCastelnuovoSeveri.poleRow, if_true]
    simp only [_root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two, Complex.conj_ofReal]
    simp only [e1]
    rw [hsum (-(1 / 2))]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [mulVec, dotProduct, ArithmeticCastelnuovoSeveri.poleRow, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, if_false, hneg]
    simp only [_root_.RHTower.WeilLevyPole.paperFT_ofReal_neg_I_div_two, Complex.conj_ofReal]
    simp only [e2]
    rw [hsum (1 / 2)]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The local block is the finite part of the pairing of the degree points.** The quadratic
form of the local Gram matrix of a family of packets at a real vector `x` is twice the product of
the degrees of the combination minus the quadratic form of Weil's Gram matrix. -/
theorem hermQuad_localGram_packets {f : ι → ℝ → ℝ} (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℝ) :
    hermQuad (ArithmeticCastelnuovoSeveri.localGram (fun n => (Λ n : ℝ))
        fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)) =
      2 * ((∫ u, packetCombination f x u * Real.exp (-u / 2)) *
          ∫ u, packetCombination f x u * Real.exp (u / 2)) -
        hermQuad (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
          fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)) := by
  obtain ⟨h0, h1⟩ := poleRow_mulVec_packets hf hfc x
  rw [ArithmeticCastelnuovoSeveri.localGram, sub_eq_add_neg, hermQuad_add, hermQuad_neg,
    hermQuad_rect_conjugate, hermQuad_polePlane, h0, h1, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The limit of the pairing of the degree points on a combination of packets is the quadratic
form of the local block of the arithmetic intersection form. -/
theorem tendsto_degreePairing_localGram {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f i u = 0) (x : ι → ℝ) :
    Tendsto (fun N : ℕ => degreeForm (packetCombination f x) (3 * K) N +
        2 * degreeContact (packetCombination f x) (3 * K) N) atTop
      (𝓝 (hermQuad (ArithmeticCastelnuovoSeveri.localGram (fun n => (Λ n : ℝ))
        fun i u => ((f i u : ℝ) : ℂ)) (fun i => ((x i : ℝ) : ℂ)))) := by
  rw [hermQuad_localGram_packets (fun i => (hf i).continuous) hfc x]
  exact tendsto_degreePairing_packetCombination hf hfc hK hsupp x

/-! ### The index law -/

/-- **The index law on the degree points.** On every finite family of packets the defect
`2 d₁ d₂ − D·D` of the pairing has at most as many negative squares as `ζ` has zeros to the
right of the critical line. -/
theorem negIndex_defect_packets_le {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
        fun i u => ((f i u : ℝ) : ℂ)) : ℕ∞) ≤
      {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard :=
  ArithmeticCastelnuovoSeveri.negIndex_weilGram_le_offLineCount _
    (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i))

/-- The arithmetic intersection form on `H, V` and a finite family of packets has at most
`1 + #{zeros with Re ρ > ½}` positive squares. -/
theorem posIndex_intersectionGram_packets_le [DecidableEq ι] {f : ι → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermPosIndex (ArithmeticCastelnuovoSeveri.intersectionGram (fun n => (Λ n : ℝ))
        fun i u => ((f i u : ℝ) : ℂ)) : ℕ∞) ≤
      1 + {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard :=
  ArithmeticCastelnuovoSeveri.posIndex_intersectionGram_le _
    (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i))

/-- **The Hodge index theorem on the degree points is the Riemann hypothesis.** RH holds iff the
arithmetic intersection form has exactly one positive square on `H, V` and every finite family
of packets. -/
theorem riemannHypothesis_iff_one_positive_square_packets :
    RiemannHypothesis ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
        hermPosIndex (ArithmeticCastelnuovoSeveri.intersectionGram (fun n => (Λ n : ℝ))
          fun i u => ((f i u : ℝ) : ℂ)) = 1 := by
  constructor
  · intro h n f hf hfc
    exact ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_one_positive_square.mp h n _
      (fun i => contDiff_ofReal_packet (hf i)) (fun i => hasCompactSupport_ofReal_packet (hfc i))
  · intro h
    refine _root_.RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr
      fun g hg hgc => ?_
    have h1 := h 1 (fun _ => g) (fun _ => hg) (fun _ => hgc)
    rw [ArithmeticCastelnuovoSeveri.posIndex_intersectionGram] at h1
    have h0 : hermNegIndex (ArithmeticCastelnuovoSeveri.weilGram (fun n => (Λ n : ℝ))
        fun (_ : Fin 1) u => ((g u : ℝ) : ℂ)) = 0 := by omega
    have hq := hermQuad_nonneg_of_negIndex_eq_zero h0 (fun _ => 1)
    rw [ArithmeticCastelnuovoSeveri.hermQuad_weilGram _ _
      (fun _ => contDiff_ofReal_packet hg) (fun _ => hasCompactSupport_ofReal_packet hgc)] at hq
    simpa using hq

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
