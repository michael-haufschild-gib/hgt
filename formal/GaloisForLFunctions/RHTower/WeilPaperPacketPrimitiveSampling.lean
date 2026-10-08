import GaloisForLFunctions.RHTower.WeilPaperPacketCoprimeFibre
import GaloisForLFunctions.RHTower.WeilWorkPBAPMomentPackets
import GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers

/-!
# Primitive rational samples of positive integer-null packet pairs

Prime-subset inclusion-exclusion removes all common multiples from a rational
packet sample. After the shared positive correction, a reduced rational sample
still recovers exactly one coefficient product. The reduced-fraction uniqueness
lemma is reused from the native vertical-progression corpus.
-/

open Matrix Complex Zeta23
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

/-- Native complex samples preserve signed differences of finite mixtures. -/
theorem mixtureSample_sub (c d : WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample (c - d) y = mixtureSample c y - mixtureSample d y :=
  map_sub (Finsupp.linearCombination ℝ _) c d

/-- Rational multiplicative diagonal on the actual packet labels. -/
def paperPacketRationalTrace {N : ℕ} (a b : PacketIndex N)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) : ℂ :=
  ∑ m : PacketIndex N, ∑ k : PacketIndex N,
    if (a : ℕ) * (k : ℕ) = (b : ℕ) * (m : ℕ) then C m k else 0

theorem paperPacketRationalTrace_sub {N : ℕ} (a b : PacketIndex N)
    (C D : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    paperPacketRationalTrace a b (C - D) =
      paperPacketRationalTrace a b C - paperPacketRationalTrace a b D := by
  simp only [paperPacketRationalTrace, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

private theorem column_rational_sample {N : ℕ} {ι : Type*} (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) (i : ι) (a b : PacketIndex N) :
    EF.weilTest (gramPacket N ((b : ℕ) + L + 1) (packetColumn A i))
      (gramPacket N ((b : ℕ) + L + 1) (packetColumn A i))
        (Real.log (a : ℕ) - Real.log (b : ℕ)) =
      (packetMass N ((b : ℕ) + L + 1) : ℂ) *
        ∑ m : PacketIndex N, ∑ k : PacketIndex N,
          if (a : ℕ) * (k : ℕ) = (b : ℕ) * (m : ℕ) then A m i * conj (A k i) else 0 := by
  have h := gramPacket_rational_sample N ((b : ℕ) + L + 1) (packetColumn A i)
    (Finset.mem_Icc.mp a.property).1 (Finset.mem_Icc.mp b.property).1 (by omega)
  rw [h]
  simp_rw [Finset.sum_subtype (p := fun m : ℕ => m ∈ Finset.Icc 1 N)
    (Finset.Icc 1 N) (fun _ => Iff.rfl)]
  simp only [packetColumn, dif_pos, Subtype.property]

/-- An actual mixture at denominator-adapted resolution has this exact rational sample. -/
theorem mixtureSample_packetColumnMixture {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (a b : PacketIndex N) :
    mixtureSample (packetColumnMixture ((b : ℕ) + L) A)
      (Real.log (a : ℕ) - Real.log (b : ℕ)) =
      (packetMass N ((b : ℕ) + L + 1) : ℂ) * paperPacketRationalTrace a b (A * Aᴴ) := by
  unfold mixtureSample
  rw [packetColumnMixture, map_sum]
  simp only [Finsupp.linearCombination_single, one_smul, gramPacketFn]
  change (∑ i, EF.weilTest (gramPacket N ((b : ℕ) + L + 1) (packetColumn A i))
    (gramPacket N ((b : ℕ) + L + 1) (packetColumn A i)) _) = _
  simp_rw [column_rational_sample L A _ a b]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  unfold paperPacketRationalTrace
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Reduced positive ratios whose numerator and denominator are actual packet labels. -/
abbrev PaperPacketCoprimePair (N : ℕ) :=
  {p : PacketIndex N × PacketIndex N // Nat.Coprime (p.1 : ℕ) (p.2 : ℕ)}

/-- Coprime masking isolates one coefficient product instead of a sum over common multiples. -/
theorem paperPacketRationalTrace_coprime {N : ℕ} (c : PacketIndex N → ℂ)
    (r : PaperPacketCoprimePair N) :
    paperPacketRationalTrace r.1.1 r.1.2 (paperPacketCoprimeCovariance c) =
      paperPacketNonunitCoeff c r.1.1 * conj (paperPacketNonunitCoeff c r.1.2) := by
  have hcond (m k : PacketIndex N) :
      ((r.1.1 : ℕ) * (k : ℕ) = (r.1.2 : ℕ) * (m : ℕ) ∧
        Nat.Coprime (m : ℕ) (k : ℕ)) ↔ m = r.1.1 ∧ k = r.1.2 := by
    constructor
    · rintro ⟨hrel, hcop⟩
      have h := VerticalAP.eq_of_coprime_of_mul_eq hcop r.property
        (by have := (Finset.mem_Icc.mp r.1.1.property).1; omega)
        (by simpa only [mul_comm] using hrel.symm)
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨Nat.mul_comm _ _, r.property⟩
  have heq (m k : PacketIndex N) :
      (if (r.1.1 : ℕ) * (k : ℕ) = (r.1.2 : ℕ) * (m : ℕ) then
        paperPacketCoprimeCovariance c m k else 0) =
      if m = r.1.1 then if k = r.1.2 then
        paperPacketNonunitCoeff c r.1.1 * conj (paperPacketNonunitCoeff c r.1.2) else 0 else 0 := by
    calc
      _ = if ((r.1.1 : ℕ) * (k : ℕ) = (r.1.2 : ℕ) * (m : ℕ) ∧
          Nat.Coprime (m : ℕ) (k : ℕ)) then
          paperPacketNonunitCoeff c m * conj (paperPacketNonunitCoeff c k) else 0 := by
        by_cases hp : (r.1.1 : ℕ) * (k : ℕ) = (r.1.2 : ℕ) * (m : ℕ) <;>
          by_cases hq : Nat.Coprime (m : ℕ) (k : ℕ) <;>
          simp [paperPacketCoprimeCovariance, hp, hq]
      _ = if m = r.1.1 ∧ k = r.1.2 then
          paperPacketNonunitCoeff c m * conj (paperPacketNonunitCoeff c k) else 0 := by
        simp only [hcond]
      _ = _ := by
        by_cases hm : m = r.1.1 <;> by_cases hk : k = r.1.2 <;> simp [hm, hk]
  unfold paperPacketRationalTrace
  simp_rw [heq]
  simp

/-- The shared positive correction preserves the reduced-rational coefficient sample exactly. -/
theorem paperPacket_prime_null_primitive_sample {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (r : PaperPacketCoprimePair N) :
    mixtureSample (paperPacketEvenPrimeNullMixture ((r.1.2 : ℕ) + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) -
      mixtureSample (paperPacketOddPrimeNullMixture ((r.1.2 : ℕ) + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) =
      (packetMass N ((r.1.2 : ℕ) + L + 1) : ℂ) *
        (paperPacketNonunitCoeff c r.1.1 * conj (paperPacketNonunitCoeff c r.1.2)) := by
  rw [← mixtureSample_sub]
  unfold paperPacketEvenPrimeNullMixture paperPacketOddPrimeNullMixture
  rw [nullRepair_paperPacket_prime_parity_sub, mixtureSample_sub]
  unfold paperPacketEvenPrimeMixture paperPacketOddPrimeMixture
  rw [mixtureSample_packetColumnMixture, mixtureSample_packetColumnMixture,
    ← mul_sub, ← paperPacketRationalTrace_sub, paperPacket_prime_covariance_difference,
    paperPacketRationalTrace_coprime]

/-- Normalizing by the actual positive bump mass recovers the coefficient product. -/
theorem paperPacket_prime_null_primitive_sample_normalized {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (r : PaperPacketCoprimePair N) :
    (mixtureSample (paperPacketEvenPrimeNullMixture ((r.1.2 : ℕ) + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) -
      mixtureSample (paperPacketOddPrimeNullMixture ((r.1.2 : ℕ) + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ))) /
      (packetMass N ((r.1.2 : ℕ) + L + 1) : ℂ) =
        paperPacketNonunitCoeff c r.1.1 * conj (paperPacketNonunitCoeff c r.1.2) := by
  rw [paperPacket_prime_null_primitive_sample]
  have hm : (packetMass N ((r.1.2 : ℕ) + L + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (packetMass_pos N ((r.1.2 : ℕ) + L + 1)).ne'
  field_simp [hm]

end RHTower.WeilWorkPBAP
