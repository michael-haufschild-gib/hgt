import GaloisForLFunctions.HyperbolicArakelovTheory.TheMassObstructionToSmoothedTorsionLocking
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Coupling smooth Green energy to torsion through ordered L² coordinates

Ordered orthogonalization of the actual logarithmic translates puts both divergent
channels on the same mass. The coordinates respect finite prefixes, so adjoining
unused degrees does not change the coupled channel. Its finite part records both
the prime discrepancy and the transformed discriminant.
-/

open MeasureTheory Filter Topology Set Finset InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ ArithmeticEffectivityTheory ArithmeticIntersectionTheory
open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis _root_.RHTower
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem normedGS_orthogonal (v : ℕ → E) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (gramSchmidtNormed ℝ v i) (gramSchmidtNormed ℝ v j) = 0 := by
  simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, gramSchmidt_orthogonal ℝ v hij, mul_zero]
private theorem normedGS_reconstruct (v : ℕ → E) (N : ℕ) {f : E}
    (hf : f ∈ Submodule.span ℝ (v '' Set.Iic N)) :
    ∑ n ∈ Iic N, inner ℝ (gramSchmidtNormed ℝ v n) f • gramSchmidtNormed ℝ v n = f := by
  rw [← span_gramSchmidt_Iic ℝ v N, ← span_gramSchmidtNormed] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_Iic.mpr hj)]
    · by_cases h : gramSchmidtNormed ℝ v j = 0
      · simp only [h, inner_zero_left, zero_smul]
      · rw [real_inner_self_eq_norm_sq, gramSchmidtNormed_unit_length' h, one_pow, one_smul]
    · intro i hi hij
      rw [normedGS_orthogonal v hij, zero_smul]
  | zero => simp only [inner_zero_right, zero_smul, sum_const_zero]
  | add f h hf hh ihf ihh =>
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, ihf, ihh]
  | smul c f hf ih =>
    simp only [inner_smul_right, mul_smul, ← Finset.smul_sum, ih]
private theorem normedGS_parseval (v : ℕ → E) (N : ℕ) {f : E}
    (hf : f ∈ Submodule.span ℝ (v '' Set.Iic N)) :
    ∑ n ∈ Iic N, (inner ℝ (gramSchmidtNormed ℝ v n) f) ^ 2 = ‖f‖ ^ 2 := by
  calc
    _ = inner ℝ (∑ n ∈ Iic N, inner ℝ (gramSchmidtNormed ℝ v n) f •
          gramSchmidtNormed ℝ v n) f := by
      simp only [sum_inner, real_inner_smul_left, pow_two]
    _ = ‖f‖ ^ 2 := by rw [normedGS_reconstruct v N hf, real_inner_self_eq_norm_sq]

/-- Logarithmic translates in real L²; the unused zeroth degree is the zero vector. -/
def smoothAtomL2 (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (n : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  if n = 0 then 0 else
    ((hg.comp (continuous_id.sub continuous_const)).memLp_of_hasCompactSupport
      (hgc.comp_homeomorph (Homeomorph.subRight (Real.log n)))).toLp
        (fun u => g (u - Real.log n))

/-- The actual L² vector of a finite smooth packet. -/
def smoothPacketL2 (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∑ n ∈ Icc 1 N, x n • smoothAtomL2 g hg hgc n

/-- Torsion coordinates in the ordered orthogonalization of smooth logarithmic atoms. -/
def gramTorsionCoordinates (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  inner ℝ (gramSchmidtNormed ℝ (smoothAtomL2 g hg hgc) n) (smoothPacketL2 g hg hgc N x)

private theorem ae_smoothAtomL2 (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {n : ℕ} (hn : n ≠ 0) :
    smoothAtomL2 g hg hgc n =ᵐ[volume] fun u => g (u - Real.log n) := by
  simp only [smoothAtomL2, if_neg hn]
  exact MemLp.coeFn_toLp _

private theorem ae_finite_l2_sum (S : Finset ℕ) (v : ℕ → Lp ℝ 2 (volume : Measure ℝ))
    (f : ℕ → ℝ → ℝ) (hv : ∀ n ∈ S, v n =ᵐ[volume] f n) :
    (fun u => (∑ n ∈ S, v n) u) =ᵐ[volume] fun u => ∑ n ∈ S, f n u := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with u hu
    exact hu
  | insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    filter_upwards [Lp.coeFn_add (v n) (∑ i ∈ S, v i), hv n (Finset.mem_insert_self _ _),
      ih (fun i hi => hv i (Finset.mem_insert_of_mem hi))] with u ha hn' hs
    exact ha.trans (congrArg₂ (· + ·) hn' hs)

/-- The finite Hilbert-space construction represents precisely the original smooth packet. -/
theorem ae_smoothPacketL2 (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) :
    smoothPacketL2 g hg hgc N x =ᵐ[volume] atomicTest N x g := by
  apply ae_finite_l2_sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  filter_upwards [Lp.coeFn_smul (x n) (smoothAtomL2 g hg hgc n),
    ae_smoothAtomL2 g hg hgc hn0] with u hmul hatom
  exact hmul.trans (congrArg (fun a : ℝ => x n * a) hatom)

private theorem packet_mem_prefix (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    smoothPacketL2 g hg hgc N x ∈
      Submodule.span ℝ (smoothAtomL2 g hg hgc '' Set.Iic N) := by
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, (Finset.mem_Icc.mp hn).2, rfl⟩)

private theorem norm_sq_smoothPacketL2 (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    ‖smoothPacketL2 g hg hgc N x‖ ^ 2 = ∫ u, atomicTest N x g u ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_smoothPacketL2 g hg hgc N x] with u hu
  rw [hu, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

@[simp] theorem gramTorsionCoordinates_zero (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    gramTorsionCoordinates g hg hgc N x 0 = 0 := by
  have hz : gramSchmidt ℝ (smoothAtomL2 g hg hgc) 0 = 0 := by
    rw [gramSchmidt_def]
    simp [smoothAtomL2]
  simp only [gramTorsionCoordinates, gramSchmidtNormed, hz, smul_zero, inner_zero_left]

/-- The coupled torsion channel has exactly the continuum mass, with no separation assumption. -/
theorem sum_sq_gramTorsionCoordinates (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, gramTorsionCoordinates g hg hgc N x n ^ 2) =
      ∫ u, atomicTest N x g u ^ 2 := by
  have h := normedGS_parseval (smoothAtomL2 g hg hgc) N (packet_mem_prefix g hg hgc N x)
  change (∑ n ∈ Iic N, gramTorsionCoordinates g hg hgc N x n ^ 2) = _ at h
  have hset : (Iic N : Finset ℕ) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp), gramTorsionCoordinates_zero,
    zero_pow (by decide), zero_add, norm_sq_smoothPacketL2] at h
  exact h

/-- Later coordinates vanish on an earlier packet. -/
theorem gramTorsionCoordinates_eq_zero_of_lt (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) {j : ℕ} (hj : N < j) :
    gramTorsionCoordinates g hg hgc N x j = 0 := by
  unfold gramTorsionCoordinates smoothPacketL2
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  have hij : i < j := lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 hj
  simp only [gramSchmidtNormed, real_inner_smul_left,
    gramSchmidt_inv_triangular ℝ (smoothAtomL2 g hg hgc) hij, mul_zero]

/-- Equal actual packets have equal coupled coordinates, even with different cutoffs. -/
theorem gramTorsionCoordinates_eq_of_packet_eq (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {N M : ℕ} {x z : ℕ → ℝ}
    (h : atomicTest N x g = atomicTest M z g) :
    gramTorsionCoordinates g hg hgc N x = gramTorsionCoordinates g hg hgc M z := by
  have hv : smoothPacketL2 g hg hgc N x = smoothPacketL2 g hg hgc M z := by
    apply Lp.ext
    exact (ae_smoothPacketL2 g hg hgc N x).trans
      (h ▸ (ae_smoothPacketL2 g hg hgc M z).symm)
  funext n
  exact congrArg (inner ℝ (gramSchmidtNormed ℝ (smoothAtomL2 g hg hgc) n)) hv

/-- The positive torsion form evaluated on the continuum-compatible coordinates. -/
def gramCoupledTorsion (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  torsionForm ρ (Icc 1 N) (gramTorsionCoordinates g hg hgc N x)

theorem gramCoupledTorsion_nonneg (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ gramCoupledTorsion g hg hgc N x ρ :=
  (weilPrimeKernel_renormalized_torsion_energy
    (S := Icc 1 N) (fun _ hn => (Finset.mem_Icc.mp hn).1)
    (gramTorsionCoordinates g hg hgc N x)).1 ρ hρ0 hρ1

/-- Pole minus the actual smooth Green energy plus the coupled positive torsion channel. -/
def gramLockedPacket (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) (c r : ℝ) : ℝ :=
  (2 * coshHalfMoment (atomicTest N x g) ^ 2 -
    2 * sinhHalfMoment (atomicTest N x g) ^ 2) - smoothGreenEnergy r (atomicTest N x g) +
      gramCoupledTorsion g hg hgc N x (smoothLockingRadius c r)

/-- The exact finite discrepancy from Weil: transformed primes and discriminant, plus normalization. -/
def gramPacketWeilDefect (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) (c : ℝ) : ℝ :=
  primeSum (atomicTest N x g) - atomicWeilForm N (gramTorsionCoordinates g hg hgc N x) +
    (c - 2 * gammaHardyPhaseRate 0) * (∫ u, atomicTest N x g u ^ 2) -
      ∑ n ∈ Icc 1 N, gramTorsionCoordinates g hg hgc N x n ^ 2 * selfIntersection n

private theorem compact_packet {g : ℝ → ℝ} (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ) : HasCompactSupport (atomicTest N x g) := by
  unfold atomicTest
  induction (Icc 1 N : Finset ℕ) using Finset.induction_on with
  | empty =>
    convert (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ)) using 1
    funext u
    exact Finset.sum_empty
  | insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    exact ((hgc.comp_homeomorph (Homeomorph.subRight (Real.log n))).mul_left).add ih

/-- Ordered Gram coupling gives finite locking for every compact C² packet, including overlaps.
The defect is computed from the actual prime form and torsion discriminant. -/
theorem tendsto_gramLockedPacket {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    Tendsto (gramLockedPacket g hg.continuous hgc N x c) (𝓝[<] 1)
      (𝓝 (weilQuad (atomicTest N x g) + gramPacketWeilDefect g hg.continuous hgc N x c)) := by
  have hT := (tendsto_torsionForm
    (S := Icc 1 N) (fun _ hn => (Finset.mem_Icc.mp hn).1)
    (gramTorsionCoordinates g hg.continuous hgc N x)).comp (tendsto_smoothLockingRadius c)
  have hA := tendsto_smoothGreenEnergy_sub_mass (atomicTest N x g)
    (contDiff_atomicTest hg N x) (compact_packet hgc N x)
  have h := ((hT.sub hA).add_const (c * ∫ u, atomicTest N x g u ^ 2)).add_const
    (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2)
  have hv : renormalizedTorsionForm (Icc 1 N) (gramTorsionCoordinates g hg.continuous hgc N x) -
      -levyEnergy (atomicTest N x g) + c * (∫ u, atomicTest N x g u ^ 2) +
      (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2) =
      weilQuad (atomicTest N x g) + gramPacketWeilDefect g hg.continuous hgc N x c := by
    rw [weilQuad_eq (contDiff_atomicTest hg N x) (compact_packet hgc N x)]
    unfold gramPacketWeilDefect renormalizedTorsionForm atomicWeilForm
    ring
  rw [hv] at h
  refine h.congr (fun r => ?_)
  simp only [Function.comp_def, log_smoothLockingRadius, sum_sq_gramTorsionCoordinates]
  dsimp only [gramLockedPacket, gramCoupledTorsion]
  ring

private theorem torsionForm_Icc_eq_of_tail {N M : ℕ} (hNM : N ≤ M)
    (y : ℕ → ℝ) (hy : ∀ j, N < j → y j = 0) (ρ : ℝ) :
    torsionForm ρ (Icc 1 M) y = torsionForm ρ (Icc 1 N) y := by
  have hsub : (Icc 1 N : Finset ℕ) ⊆ Icc 1 M := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hNM⟩
  unfold torsionForm
  calc
    _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 M, y m * y n * twistedEnergy ρ m n := by
      symm
      apply Finset.sum_subset hsub
      intro m hm hmN
      have hm' : N < m := by
        simp only [Finset.mem_Icc] at hm hmN
        omega
      simp only [hy m hm', zero_mul, Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      symm
      apply Finset.sum_subset hsub
      intro n hn hnN
      have hn' : N < n := by
        simp only [Finset.mem_Icc] at hn hnN
        omega
      simp only [hy n hn', mul_zero, zero_mul]

/-- Coupling is intrinsic to the actual packet for a fixed profile, independently of cutoff. -/
theorem gramCoupledTorsion_eq_of_packet_eq (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {N M : ℕ} {x z : ℕ → ℝ}
    (h : atomicTest N x g = atomicTest M z g) (ρ : ℝ) :
    gramCoupledTorsion g hg hgc N x ρ = gramCoupledTorsion g hg hgc M z ρ := by
  have hy := gramTorsionCoordinates_eq_of_packet_eq g hg hgc h
  unfold gramCoupledTorsion
  rcases le_total N M with hNM | hMN
  · rw [← hy]
    exact (torsionForm_Icc_eq_of_tail hNM _
      (fun j hj => gramTorsionCoordinates_eq_zero_of_lt g hg hgc N x hj) ρ).symm
  · rw [hy]
    exact torsionForm_Icc_eq_of_tail hMN _
      (fun j hj => gramTorsionCoordinates_eq_zero_of_lt g hg hgc M z hj) ρ

/-- The whole locked family respects equality of smooth packets and zero-padding. -/
theorem gramLockedPacket_eq_of_packet_eq (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {N M : ℕ} {x z : ℕ → ℝ}
    (h : atomicTest N x g = atomicTest M z g) (c r : ℝ) :
    gramLockedPacket g hg hgc N x c r = gramLockedPacket g hg hgc M z c r := by
  unfold gramLockedPacket
  rw [h, gramCoupledTorsion_eq_of_packet_eq g hg hgc h]

private theorem gramSchmidt_eq_of_prefix_orthogonal (v : ℕ → E) (N : ℕ)
    (hv : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ∀ j ≤ N, gramSchmidt ℝ v j = v j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hsum : (∑ i ∈ Iio j,
        (inner ℝ (gramSchmidt ℝ v i) (v j) / ‖gramSchmidt ℝ v i‖ ^ 2) •
          gramSchmidt ℝ v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i < j := Finset.mem_Iio.mp hi
      rw [ih i hij (hij.le.trans hj), hv i (hij.le.trans hj) j hj hij.ne]
      simp only [zero_div, zero_smul]
    have h := gramSchmidt_def'' ℝ v j
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [hsum, add_zero] at h
    exact h.symm

private theorem smoothAtomL2_inner (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    inner ℝ (smoothAtomL2 g hg hgc i) (smoothAtomL2 g hg hgc j) =
      ∫ u, g (u - Real.log i) * g (u - Real.log j) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_smoothAtomL2 g hg hgc hi, ae_smoothAtomL2 g hg hgc hj] with u hui huj
  rw [hui, huj]
  exact real_inner_comm _ _

private theorem smoothAtomL2_norm (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {i : ℕ} (hi : i ≠ 0) :
    ‖smoothAtomL2 g hg hgc i‖ = Real.sqrt (∫ u, g u ^ 2) := by
  have h : ‖smoothAtomL2 g hg hgc i‖ ^ 2 = ∫ u, g u ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, smoothAtomL2_inner g hg hgc hi hi]
    simp only [← pow_two]
    exact integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log i)
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

private theorem separated_atoms_orthogonal (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {w : ℝ} (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hw : w < atomSpacing N) :
    ∀ i ≤ N, ∀ j ≤ N, i ≠ j →
      inner ℝ (smoothAtomL2 g hg hgc i) (smoothAtomL2 g hg hgc j) = 0 := by
  intro i hi j hj hij
  by_cases hi0 : i = 0
  · simp [hi0, smoothAtomL2]
  by_cases hj0 : j = 0
  · simp [hj0, smoothAtomL2]
  rw [smoothAtomL2_inner g hg hgc hi0 hj0]
  have hzero : (fun u => g (u - Real.log i) * g (u - Real.log j)) = fun _ => 0 := by
    funext u
    exact bump_mul_eq_zero hsupp hw (Nat.one_le_iff_ne_zero.mpr hi0)
      (Nat.one_le_iff_ne_zero.mpr hj0) ((min_le_left i j).trans hi) hij u
  rw [hzero]
  exact integral_zero _ _

/-- Below the atom spacing, ordered coupling recovers the original profile-mass scaling. -/
theorem gramTorsionCoordinates_of_separated (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {w : ℝ} (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    gramTorsionCoordinates g hg hgc N x i = Real.sqrt (∫ u, g u ^ 2) * x i := by
  have hi0 : i ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hi).1
  have horth := separated_atoms_orthogonal g hg hgc hsupp hw
  have hgs := gramSchmidt_eq_of_prefix_orthogonal (smoothAtomL2 g hg hgc) N horth
  unfold gramTorsionCoordinates
  rw [gramSchmidtNormed, hgs i (Finset.mem_Icc.mp hi).2, real_inner_smul_left]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  unfold smoothPacketL2
  rw [inner_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [inner_smul_right, real_inner_self_eq_norm_sq, smoothAtomL2_norm g hg hgc hi0]
    by_cases hm : Real.sqrt (∫ u, g u ^ 2) = 0
    · simp only [hm, inv_zero, zero_mul]
    · field_simp
  · intro j hj hji
    rw [inner_smul_right, horth i (Finset.mem_Icc.mp hi).2 j (Finset.mem_Icc.mp hj).2 hji.symm,
      mul_zero]

/-- The coupled and scalar-locked energies coincide exactly on separated packets. -/
theorem gramLockedPacket_of_separated {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) {w : ℝ} (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) (c r : ℝ) :
    gramLockedPacket g hg.continuous hgc N x c r = smoothLockedPacket c r N x g := by
  have hmass : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg (fun u => sq_nonneg (g u))
  unfold gramLockedPacket smoothLockedPacket
  congr 1
  unfold gramCoupledTorsion torsionForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [gramTorsionCoordinates_of_separated g hg.continuous hgc hsupp hw x hm,
    gramTorsionCoordinates_of_separated g hg.continuous hgc hsupp hw x hn]
  calc
    _ = (Real.sqrt (∫ u, g u ^ 2) * Real.sqrt (∫ u, g u ^ 2)) *
      (x m * x n * twistedEnergy (smoothLockingRadius c r) m n) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hmass]

#print axioms gramLockedPacket_of_separated
#print axioms gramLockedPacket_eq_of_packet_eq
#print axioms gramCoupledTorsion_nonneg
#print axioms sum_sq_gramTorsionCoordinates
#print axioms gramTorsionCoordinates_eq_of_packet_eq
#print axioms tendsto_gramLockedPacket

end GaloisForLFunctions.HyperbolicArakelovTheory
