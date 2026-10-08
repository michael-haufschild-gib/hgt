import GaloisForLFunctions.RHTower.WeilPaperPacketPrimitiveSampling

/-!
# Independent finite rational samples inside positive integer-null fibres

Ordered coprime nonunit packet labels index independent rational observations.
Two-label coefficient vectors and the paper's prime-subset masks isolate each
such observation. Summing actual positive repaired pairs prescribes all these
complex sample differences simultaneously, with equal total mass.
-/

open Complex
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- One orientation of each coprime pair of nonunit packet labels. -/
abbrev PaperPacketPrimitiveEdge (N : ℕ) :=
  {p : PacketIndex N × PacketIndex N //
    1 < (p.1 : ℕ) ∧ (p.1 : ℕ) < (p.2 : ℕ) ∧ Nat.Coprime (p.1 : ℕ) (p.2 : ℕ)}

private def edgeRatio {N : ℕ} (e : PaperPacketPrimitiveEdge N) : PaperPacketCoprimePair N :=
  ⟨e.1, e.property.2.2⟩

/-- A common denominator resolution works for every reduced ratio in the packet. -/
theorem paperPacket_prime_null_primitive_sample_uniform {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (r : PaperPacketCoprimePair N) :
    mixtureSample (paperPacketEvenPrimeNullMixture (N + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) -
      mixtureSample (paperPacketOddPrimeNullMixture (N + L) c)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) =
      (packetMass N (N + L + 1) : ℂ) *
        (paperPacketNonunitCoeff c r.1.1 * conj (paperPacketNonunitCoeff c r.1.2)) := by
  have hb := (Finset.mem_Icc.mp r.1.2.property).2
  have heq : (r.1.2 : ℕ) + (N - (r.1.2 : ℕ) + L) = N + L := by omega
  simpa only [heq] using
    paperPacket_prime_null_primitive_sample (N - (r.1.2 : ℕ) + L) c r

/-- A two-label vector encoding one oriented complex coefficient. -/
def paperPacketEdgeCoeff {N : ℕ} (e : PaperPacketPrimitiveEdge N) (z : ℂ)
    (m : PacketIndex N) : ℂ :=
  if m = e.1.1 then z else if m = e.1.2 then 1 else 0

/-- Coprime masking turns two-label vectors into a delta basis on ordered reduced ratios. -/
theorem paperPacketEdgeCoeff_primitive_product {N : ℕ}
    (e r : PaperPacketPrimitiveEdge N) (z : ℂ) :
    paperPacketNonunitCoeff (paperPacketEdgeCoeff e z) r.1.1 *
      conj (paperPacketNonunitCoeff (paperPacketEdgeCoeff e z) r.1.2) =
        if r = e then z else 0 := by
  have hr1 : (r.1.1 : ℕ) ≠ 1 := by have := r.property.1; omega
  have hr2 : (r.1.2 : ℕ) ≠ 1 := by
    have := r.property.1
    have := r.property.2.1
    omega
  simp only [paperPacketNonunitCoeff, if_neg hr1, if_neg hr2]
  have hrr : r.1.1 ≠ r.1.2 := by
    intro h
    have hv := congrArg Subtype.val h
    have := r.property.2.1
    omega
  by_cases hre : r = e
  · subst r
    simp [paperPacketEdgeCoeff, Ne.symm hrr]
  rw [if_neg hre]
  by_cases ha : r.1.1 = e.1.1
  · have hb : r.1.2 ≠ e.1.2 := by
      intro h
      exact hre (Subtype.ext (Prod.ext ha h))
    have hba : r.1.2 ≠ e.1.1 := fun h => hrr (ha.trans h.symm)
    simp [paperPacketEdgeCoeff, ha, hb, hba]
  by_cases hab : r.1.1 = e.1.2
  · have hbb : r.1.2 ≠ e.1.2 := fun h => hrr (hab.trans h.symm)
    have hba : r.1.2 ≠ e.1.1 := by
      intro h
      have hv := congrArg Subtype.val hab
      have hw := congrArg Subtype.val h
      have := r.property.2.1
      have := e.property.2.1
      omega
    simp [paperPacketEdgeCoeff, hba, hbb]
  simp [paperPacketEdgeCoeff, ha, hab]

private theorem edge_null_equal_mass {N : ℕ} (L : ℕ)
    (e : PaperPacketPrimitiveEdge N) (z : ℂ) :
    mixtureSample (paperPacketEvenPrimeNullMixture (N + L) (paperPacketEdgeCoeff e z)) 0 =
      mixtureSample (paperPacketOddPrimeNullMixture (N + L) (paperPacketEdgeCoeff e z)) 0 := by
  have hN : 1 ≤ N := by
    have := (Finset.mem_Icc.mp e.1.1.property).2
    have := e.property.1
    omega
  let u : PacketIndex N := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  let r : PaperPacketCoprimePair N := ⟨(u, u), by simp [u]⟩
  apply sub_eq_zero.mp
  simpa [r, u, paperPacketNonunitCoeff] using
    paperPacket_prime_null_primitive_sample_uniform L (paperPacketEdgeCoeff e z) r

theorem mixtureSample_sum {ι : Type*} [Fintype ι]
    (c : ι → WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample (∑ i, c i) y = ∑ i, mixtureSample (c i) y := by
  unfold mixtureSample
  rw [map_sum]

/-- Positive side of the simultaneous primitive-sample interpolation. -/
def paperPacketEdgeEvenMixture {N : ℕ} (L : ℕ) (z : PaperPacketPrimitiveEdge N → ℂ) :
    WeilTestFn →₀ ℝ :=
  ∑ e, paperPacketEvenPrimeNullMixture (N + L)
    (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ)))

/-- The second positive side; subtraction is used only when observing the pair. -/
def paperPacketEdgeOddMixture {N : ℕ} (L : ℕ) (z : PaperPacketPrimitiveEdge N → ℂ) :
    WeilTestFn →₀ ℝ :=
  ∑ e, paperPacketOddPrimeNullMixture (N + L)
    (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ)))

theorem paperPacketEdgeEvenMixture_nonneg {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) (f : WeilTestFn) :
    0 ≤ paperPacketEdgeEvenMixture L z f := by
  have h : 0 ≤ paperPacketEdgeEvenMixture L z :=
    Finset.sum_nonneg fun e _ => paperPacketEvenPrimeNullMixture_nonneg (N + L) _
  exact h f

theorem paperPacketEdgeOddMixture_nonneg {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) (f : WeilTestFn) :
    0 ≤ paperPacketEdgeOddMixture L z f := by
  have h : 0 ≤ paperPacketEdgeOddMixture L z :=
    Finset.sum_nonneg fun e _ => paperPacketOddPrimeNullMixture_nonneg (N + L) _
  exact h f

@[simp] theorem defect_paperPacketEdgeEvenMixture {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) : defect (paperPacketEdgeEvenMixture L z) = 0 := by
  simp [paperPacketEdgeEvenMixture, map_sum]

@[simp] theorem defect_paperPacketEdgeOddMixture {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) : defect (paperPacketEdgeOddMixture L z) = 0 := by
  simp [paperPacketEdgeOddMixture, map_sum]

theorem paperPacketEdgeMixture_equal_mass {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) :
    mixtureSample (paperPacketEdgeEvenMixture L z) 0 =
      mixtureSample (paperPacketEdgeOddMixture L z) 0 := by
  simp only [paperPacketEdgeEvenMixture, paperPacketEdgeOddMixture, mixtureSample_sum]
  exact Finset.sum_congr rfl fun e _ => edge_null_equal_mass L e _

/-- All ordered primitive rational observations are prescribed independently and exactly. -/
theorem paperPacketEdgeMixture_rational_difference {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) (r : PaperPacketPrimitiveEdge N) :
    mixtureSample (paperPacketEdgeEvenMixture L z)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) -
      mixtureSample (paperPacketEdgeOddMixture L z)
        (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) = z r := by
  simp only [paperPacketEdgeEvenMixture, paperPacketEdgeOddMixture, mixtureSample_sum,
    ← Finset.sum_sub_distrib]
  change (∑ e : PaperPacketPrimitiveEdge N, (mixtureSample (paperPacketEvenPrimeNullMixture (N + L)
      (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ))))
        (Real.log ((edgeRatio r).1.1 : ℕ) - Real.log ((edgeRatio r).1.2 : ℕ)) -
      mixtureSample (paperPacketOddPrimeNullMixture (N + L)
      (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ))))
        (Real.log ((edgeRatio r).1.1 : ℕ) - Real.log ((edgeRatio r).1.2 : ℕ)))) = _
  simp_rw [paperPacket_prime_null_primitive_sample_uniform]
  change (∑ e : PaperPacketPrimitiveEdge N, (packetMass N (N + L + 1) : ℂ) *
    (paperPacketNonunitCoeff (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ))) r.1.1 *
      conj (paperPacketNonunitCoeff
        (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ))) r.1.2))) = _
  simp_rw [paperPacketEdgeCoeff_primitive_product]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hm : (packetMass N (N + L + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (packetMass_pos N (N + L + 1)).ne'
  field_simp [hm]

/-- Simultaneous interpolation retains the exact full energy of every coprime edge. -/
theorem paperPacketEdgeMixture_energy_difference {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) :
    energy (paperPacketEdgeEvenMixture L z) - energy (paperPacketEdgeOddMixture L z) =
      ∑ e, packetArchPairing (N + L + 1) (paperPacketCoprimeCovariance
        (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ)))) := by
  simp only [paperPacketEdgeEvenMixture, paperPacketEdgeOddMixture, map_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => energy_paperPacket_prime_null_parity (N + L) _

/-- Simultaneous finite rational freedom inside the actual positive all-integer-null cone. -/
theorem exists_positive_null_equal_mass_pair_primitive_interpolation {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧ defect a = 0 ∧ defect b = 0 ∧
      mixtureSample a 0 = mixtureSample b 0 ∧
      energy a - energy b =
        (∑ e, packetArchPairing (N + L + 1) (paperPacketCoprimeCovariance
          (paperPacketEdgeCoeff e (z e / (packetMass N (N + L + 1) : ℂ))))) ∧
      ∀ r : PaperPacketPrimitiveEdge N,
        mixtureSample a (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) -
          mixtureSample b (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) = z r :=
  ⟨paperPacketEdgeEvenMixture L z, paperPacketEdgeOddMixture L z,
    paperPacketEdgeEvenMixture_nonneg L z, paperPacketEdgeOddMixture_nonneg L z,
    defect_paperPacketEdgeEvenMixture L z, defect_paperPacketEdgeOddMixture L z,
    paperPacketEdgeMixture_equal_mass L z, paperPacketEdgeMixture_energy_difference L z,
    paperPacketEdgeMixture_rational_difference L z⟩

/-- Every finite primitive sample vector has a signed interpolant with zero mass
and every integer constraint zero, obtained from two actual positive mixtures. -/
theorem exists_integer_null_zero_mass_primitive_interpolant {N : ℕ} (L : ℕ)
    (z : PaperPacketPrimitiveEdge N → ℂ) :
    ∃ d : WeilTestFn →₀ ℝ, defect d = 0 ∧ mixtureSample d 0 = 0 ∧
      ∀ r : PaperPacketPrimitiveEdge N,
        mixtureSample d (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) = z r := by
  obtain ⟨a, b, _, _, ha, hb, hm, _, hs⟩ :=
    exists_positive_null_equal_mass_pair_primitive_interpolation L z
  refine ⟨a - b, ?_, ?_, ?_⟩
  · rw [map_sub, ha, hb, sub_self]
  · rw [mixtureSample_sub, hm, sub_self]
  · intro r
    rw [mixtureSample_sub]
    exact hs r

end RHTower.WeilWorkPBAP
