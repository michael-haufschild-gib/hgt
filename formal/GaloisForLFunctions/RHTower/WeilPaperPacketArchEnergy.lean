import GaloisForLFunctions.RHTower.WeilWorkPBAPGramPackets
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy

/-!
# Full archimedean packet energy and the Crouzeix covariance gap

The full pole-plus-archimedean energy of a finite complex packet family is an
exact pairing of its covariance matrix with a fixed translated-bump kernel.
The positive-block identity from the Crouzeix paper therefore controls changes
in this actual Weil energy, with no assumption that the kernel is positive.
-/

open Matrix Complex MeasureTheory Zeta23 GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

private def packetColumn {N : ℕ} {ι : Type*}
    (A : Matrix (PacketIndex N) ι ℂ) (i : ι) (m : ℕ) : ℂ :=
  if hm : m ∈ Finset.Icc 1 N then A ⟨m, hm⟩ i else 0

/-- The exact translated correlation kernel, including both pole terms. -/
def packetArchKernel (N L : ℕ) : Matrix (PacketIndex N) (PacketIndex N) ℂ :=
  fun m k => weilFullFunctional 0
    (transl (resPt N m - resPt N k)
      (EF.weilTest (narrowBumpC (N * L)) (narrowBumpC (N * L))))

/-- Pair a packet covariance with its full archimedean kernel. -/
def packetArchPairing {N : ℕ} (L : ℕ)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) : ℝ :=
  (∑ m, ∑ k, C m k * packetArchKernel N L m k).re

/-- Full pole-plus-archimedean energy of the actual smooth packet family. -/
def packetArchEnergy {N : ℕ} {ι : Type*} [Fintype ι] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) : ℝ :=
  ∑ i, weilArchRe (EF.weilTest (gramPacket N L (packetColumn A i))
    (gramPacket N L (packetColumn A i)))

private theorem weilArchRe_eq (k : ℝ → ℂ) :
    weilArchRe k = (weilFullFunctional 0 k).re := by
  simp [weilArchRe, weilFullFunctional]

private theorem packet_correlation {N : ℕ} {ι : Type*}
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (i : ι) :
    EF.weilTest (gramPacket N L (packetColumn A i))
      (gramPacket N L (packetColumn A i)) =
        ∑ m : PacketIndex N, ∑ k : PacketIndex N,
          (A m i * conj (A k i)) • transl (resPt N m - resPt N k)
            (EF.weilTest (narrowBumpC (N * L)) (narrowBumpC (N * L))) := by
  funext y
  change EF.weilTest
    (fun u => ∑ m ∈ Finset.Icc 1 N, packetColumn A i m * narrowBumpC (N * L) (u - resPt N m))
    (fun u => ∑ m ∈ Finset.Icc 1 N, packetColumn A i m * narrowBumpC (N * L) (u - resPt N m)) y = _
  rw [weilTest_sum_translates (contDiff_narrowBumpC _).continuous
    (hasCompactSupport_narrowBumpC _)]
  simp_rw [Finset.sum_subtype (p := fun m : ℕ => m ∈ Finset.Icc 1 N)
    (Finset.Icc 1 N) (fun _ => Iff.rfl)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, packetColumn,
    dif_pos, Subtype.property, transl]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

private theorem packet_functional {N : ℕ} {ι : Type*}
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (i : ι) :
    weilFullFunctional 0 (EF.weilTest (gramPacket N L (packetColumn A i))
      (gramPacket N L (packetColumn A i))) =
        ∑ m, ∑ k, (A m i * conj (A k i)) * packetArchKernel N L m k := by
  have hb := admissible_weilTest
    ((contDiff_narrowBumpC (N * L)).of_le (by norm_cast))
    (hasCompactSupport_narrowBumpC (N * L))
  rw [packet_correlation]
  rw [weilFullFunctional_sum 0 _ (fun m _ => Admissible.sum _
    (fun k _ => (hb.transl _).smul _))]
  apply Finset.sum_congr rfl
  intro m _
  rw [weilFullFunctional_sum 0 _ (fun k _ => (hb.transl _).smul _)]
  simp only [weilFullFunctional_smul, packetArchKernel]

/-- Exact mixed signed/complex packet energy, expressed through the native covariance. -/
theorem packetArchEnergy_eq_covariance {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    packetArchEnergy L A = packetArchPairing L (A * Aᴴ) := by
  unfold packetArchEnergy packetArchPairing
  simp_rw [weilArchRe_eq, packet_functional, ← Complex.re_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← Finset.sum_mul,
    Complex.star_def]

theorem packetArchPairing_sub {N : ℕ} (L : ℕ)
    (C D : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    packetArchPairing L (C - D) = packetArchPairing L C - packetArchPairing L D := by
  simp only [packetArchPairing, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib, Complex.sub_re]

/-- The full kernel controls every signed covariance perturbation. -/
theorem packetArchPairing_sq_le {N : ℕ} (L : ℕ)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    packetArchPairing L C ^ 2 ≤
      finiteMatrixHilbertSchmidtSq C * finiteMatrixHilbertSchmidtSq (packetArchKernel N L) := by
  have hn : |packetArchPairing L C| ≤
      ∑ m, ∑ k, ‖C m k‖ * ‖packetArchKernel N L m k‖ := by
    calc
      _ ≤ ‖∑ m, ∑ k, C m k * packetArchKernel N L m k‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ m, ‖∑ k, C m k * packetArchKernel N L m k‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun m _ => by simpa only [norm_mul] using
        (norm_sum_le (s := Finset.univ) (fun k => C m k * packetArchKernel N L m k))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product (Finset.univ : Finset (PacketIndex N)))
    (fun p => ‖C p.1 p.2‖) (fun p => ‖packetArchKernel N L p.1 p.2‖)
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq,
    finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  have hsq := pow_le_pow_left₀ (abs_nonneg (packetArchPairing L C)) hn 2
  rw [sq_abs] at hsq
  exact hsq.trans (by simpa only [Finset.product_eq_sprod, Finset.sum_product] using hcs)

/-- The Crouzeix gap bounds the change in full Weil packet energy. -/
theorem packetArchEnergy_sub_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    (packetArchEnergy L A - packetArchEnergy L B) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          finiteMatrixHilbertSchmidtSq (packetArchKernel N L) := by
  rw [packetArchEnergy_eq_covariance, packetArchEnergy_eq_covariance,
    ← packetArchPairing_sub, crouzeix_gram_energy_identity]
  exact packetArchPairing_sq_le L _

/-- Refactorizing a packet covariance preserves its entire archimedean energy. -/
theorem packetArchEnergy_eq_of_covariance_eq {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (h : A * Aᴴ = B * Bᴴ) : packetArchEnergy L A = packetArchEnergy L B := by
  rw [packetArchEnergy_eq_covariance, packetArchEnergy_eq_covariance, h]

end RHTower.WeilWorkPBAP
