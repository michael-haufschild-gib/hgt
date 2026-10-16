import GaloisForLFunctions.RHTower.PaperThetaNativeRootTransport
import GaloisForLFunctions.RHTower.PaperThetaCompactMeyerRealization

/-! # Full native generalized-root completeness in original Meyer sources

The original full-multiplicity Meyer packets exhaust, rather than merely
embed in, the generalized-root spaces of the actual compact native inverse.
The whole-space quantile comparison rules out every additional native chain.
-/

noncomputable section
open Complex Set Module.End
open scoped BoundedContinuousFunction Classical

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource

theorem nativePencil_pow_kernel_iff (rho : XiDivisorSupport) (n : ℕ)
    (v : NativeContinuousSpace) :
    ((nativePencil (xiSpectralPointSupport rho)).toLinearMap ^ n) v = 0 ↔
      ((nativeCompactResolvent.toLinearMap-nativeXiResolventValue rho • 1) ^ n) v = 0 := by
  let z := xiSpectralPointSupport rho
  have hIz : I-z ≠ 0 := sub_ne_zero.mpr
    (sub_ne_zero.mp (xiSpectralPointSupport_sub_I_ne_zero rho)).symm
  have hs : (I-z)*nativeXiResolventValue rho = -1 := by
    rw [nativeXiResolventValue, show I-z = -(z-I) from by ring, neg_mul,
      mul_inv_cancel₀ (xiSpectralPointSupport_sub_I_ne_zero rho)]
  have he : (nativePencil z).toLinearMap =
      (I-z) • (nativeCompactResolvent.toLinearMap-nativeXiResolventValue rho • 1) := by
    apply LinearMap.ext
    intro u
    change u+(I-z) • nativeCompactResolvent u =
      (I-z) • (nativeCompactResolvent u-nativeXiResolventValue rho • u)
    rw [smul_sub, smul_smul, hs, neg_one_smul]
    abel
  change ((nativePencil z).toLinearMap ^ n) v = 0 ↔ _
  rw [he, smul_pow, LinearMap.smul_apply]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero n hIz)
  · intro h
    rw [h, smul_zero]

def nativeFiniteBasis (S : Finset XiDivisorSupport) (q : DeningerMeyerFiniteXiJetSlot S) :
    NativeContinuousSpace := nativeFiniteSynthesis S (Pi.single q 1)

theorem nativePencil_basis (S : Finset XiDivisorSupport) (q : DeningerMeyerFiniteXiJetSlot S) :
    nativePencil (xiSpectralPointSupport q.1.1) (nativeFiniteBasis S q) =
      if h : q.2.val = 0 then 0 else
        nativeCompactResolvent (nativeFiniteBasis S ⟨q.1,⟨q.2.val-1,by omega⟩⟩) := by
  have he := nativeCompactResolvent_finite_shift S (Pi.single q 1)
  simp only [thetaFinitePacketGenerator, Fintype.linearCombination_apply_single,
    one_smul, thetaFiniteStep] at he
  by_cases h : q.2.val = 0
  · simp only [h, dite_true, map_sub, map_smul, add_zero] at he
    rw [dif_pos h]
    change nativeFiniteBasis S q+(I-xiSpectralPointSupport q.1.1) •
      nativeCompactResolvent (nativeFiniteBasis S q) = 0
    change xiSpectralPointSupport q.1.1 • nativeCompactResolvent (nativeFiniteBasis S q)-
      I • nativeCompactResolvent (nativeFiniteBasis S q) = nativeFiniteBasis S q at he
    calc
      _ = (xiSpectralPointSupport q.1.1 • nativeCompactResolvent (nativeFiniteBasis S q)-
          I • nativeCompactResolvent (nativeFiniteBasis S q))+
          (I-xiSpectralPointSupport q.1.1) • nativeCompactResolvent (nativeFiniteBasis S q) :=
        congrArg (fun f => f+(I-xiSpectralPointSupport q.1.1) •
          nativeCompactResolvent (nativeFiniteBasis S q)) he.symm
      _ = 0 := by module
  · simp only [h, dite_false, map_sub, map_add, map_smul] at he
    rw [dif_neg h]
    let p : DeningerMeyerFiniteXiJetSlot S := ⟨q.1,⟨q.2.val-1,by omega⟩⟩
    change nativeFiniteBasis S q+(I-xiSpectralPointSupport q.1.1) •
      nativeCompactResolvent (nativeFiniteBasis S q) = nativeCompactResolvent (nativeFiniteBasis S p)
    change xiSpectralPointSupport q.1.1 • nativeCompactResolvent (nativeFiniteBasis S q)+
      nativeCompactResolvent (nativeFiniteBasis S p)-
      I • nativeCompactResolvent (nativeFiniteBasis S q) = nativeFiniteBasis S q at he
    calc
      _ = (xiSpectralPointSupport q.1.1 • nativeCompactResolvent (nativeFiniteBasis S q)+
          nativeCompactResolvent (nativeFiniteBasis S p)-
          I • nativeCompactResolvent (nativeFiniteBasis S q))+
          (I-xiSpectralPointSupport q.1.1) • nativeCompactResolvent (nativeFiniteBasis S q) :=
        congrArg (fun f => f+(I-xiSpectralPointSupport q.1.1) •
          nativeCompactResolvent (nativeFiniteBasis S q)) he.symm
      _ = _ := by module

private theorem nativePencil_resolvent_commute (z : ℂ) :
    Commute (nativePencil z).toLinearMap nativeCompactResolvent.toLinearMap := by
  apply LinearMap.ext
  intro v
  change nativeCompactResolvent v+(I-z) • nativeCompactResolvent (nativeCompactResolvent v) =
    nativeCompactResolvent (v+(I-z) • nativeCompactResolvent v)
  rw [map_add, map_smul]

theorem nativeFiniteBasis_pencil_power (S : Finset XiDivisorSupport) (rho : ↥S)
    (n : ℕ) (hn : n < xiSupportMultiplicity rho.1) :
    ((nativePencil (xiSpectralPointSupport rho.1)).toLinearMap ^ (n+1))
      (nativeFiniteBasis S ⟨rho,⟨n,hn⟩⟩) = 0 := by
  induction n with
  | zero =>
      simpa using nativePencil_basis S ⟨rho,⟨0,hn⟩⟩
  | succ n ih =>
      have hnp : n < xiSupportMultiplicity rho.1 := by omega
      have hc := congrArg (fun T : Module.End ℂ NativeContinuousSpace =>
        T (nativeFiniteBasis S ⟨rho,⟨n,hnp⟩⟩))
        ((nativePencil_resolvent_commute (xiSpectralPointSupport rho.1)).pow_left (n+1)).eq
      rw [pow_succ]
      change ((nativePencil (xiSpectralPointSupport rho.1)).toLinearMap ^ (n+1))
        (nativePencil (xiSpectralPointSupport rho.1)
          (nativeFiniteBasis S ⟨rho,⟨n+1,hn⟩⟩)) = 0
      rw [nativePencil_basis S ⟨rho,⟨n+1,hn⟩⟩, dif_neg (Nat.succ_ne_zero n)]
      change ((nativePencil (xiSpectralPointSupport rho.1)).toLinearMap ^ (n+1))
        (nativeCompactResolvent (nativeFiniteBasis S ⟨rho,⟨n,hnp⟩⟩)) = 0
      rw [show ((nativePencil (xiSpectralPointSupport rho.1)).toLinearMap ^ (n+1))
          (nativeCompactResolvent (nativeFiniteBasis S ⟨rho,⟨n,hnp⟩⟩)) =
          nativeCompactResolvent (((nativePencil (xiSpectralPointSupport rho.1)).toLinearMap ^ (n+1))
            (nativeFiniteBasis S ⟨rho,⟨n,hnp⟩⟩)) from hc,
        ih hnp, map_zero]

theorem nativeFiniteSynthesis_singleton_le_root (rho : XiDivisorSupport) :
    LinearMap.range (nativeFiniteSynthesis {rho}) ≤ NativeXiRootBlock rho := by
  have hslot (q : DeningerMeyerFiniteXiJetSlot {rho}) :
      nativeFiniteBasis {rho} q ∈ NativeXiRootBlock rho := by
    rcases q with ⟨⟨tau,htau⟩,j⟩
    have ht : tau = rho := Finset.mem_singleton.mp htau
    subst tau
    apply (mem_maxGenEigenspace _ _ _).mpr
    refine ⟨j.val+1,(nativePencil_pow_kernel_iff rho (j.val+1) _).mp ?_⟩
    exact nativeFiniteBasis_pencil_power {rho} ⟨rho,htau⟩ j.val j.isLt
  rintro f ⟨c,rfl⟩
  change (∑ q : DeningerMeyerFiniteXiJetSlot {rho},
    c q • ((q.2.val.factorial : ℂ)⁻¹ • nativeThetaDivisorJet q.1.1 q.2)) ∈ NativeXiRootBlock rho
  apply Submodule.sum_mem
  intro q _
  apply Submodule.smul_mem
  simpa only [nativeFiniteBasis, nativeFiniteSynthesis, Fintype.linearCombination_apply_single,
    one_smul] using hslot q

theorem nativeFiniteSynthesis_singleton_finrank (rho : XiDivisorSupport) :
    Module.finrank ℂ (LinearMap.range (nativeFiniteSynthesis {rho})) = xiSupportMultiplicity rho := by
  rw [LinearMap.finrank_range_of_inj (nativeFiniteSynthesis_injective {rho})]
  simp [DeningerMeyerFiniteXiJetPacket, DeningerMeyerFiniteXiJetSlot,
    DeningerArithmeticJetIndex, Fintype.card_sigma]

/-- Full completeness: no bounded continuous generalized Xi mode lies outside
the literal original full-multiplicity Meyer packet. -/
theorem nativeXiRootBlock_eq_original_packet (rho : XiDivisorSupport) :
    NativeXiRootBlock rho = LinearMap.range (nativeFiniteSynthesis {rho}) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (nativeFiniteSynthesis_singleton_le_root rho)
  rw [nativeFiniteSynthesis_singleton_finrank]
  exact finrank_nativeXiRootBlock_le rho

theorem finrank_nativeXiRootBlock (rho : XiDivisorSupport) :
    Module.finrank ℂ (NativeXiRootBlock rho) = xiSupportMultiplicity rho := by
  rw [nativeXiRootBlock_eq_original_packet, nativeFiniteSynthesis_singleton_finrank]

def nativeXiRootSynthesis (rho : XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket {rho} →ₗ[ℂ] NativeXiRootBlock rho where
  toFun c := ⟨nativeFiniteSynthesis {rho} c,
    nativeFiniteSynthesis_singleton_le_root rho ⟨c,rfl⟩⟩
  map_add' c d := Subtype.ext (map_add _ c d)
  map_smul' a c := Subtype.ext (map_smul _ a c)

theorem nativeXiRootSynthesis_bijective (rho : XiDivisorSupport) :
    Function.Bijective (nativeXiRootSynthesis rho) := by
  constructor
  · intro c d h
    exact nativeFiniteSynthesis_injective {rho} (congrArg Subtype.val h)
  · intro v
    have hv : v.val ∈ LinearMap.range (nativeFiniteSynthesis {rho}) :=
      (nativeXiRootBlock_eq_original_packet rho).le v.property
    obtain ⟨c,hc⟩ := hv
    exact ⟨c,Subtype.ext hc⟩

/-- Canonical coordinates for the entire original-space generalized block. -/
def nativeXiRootCoordinates (rho : XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket {rho} ≃ₗ[ℂ] NativeXiRootBlock rho :=
  LinearEquiv.ofBijective (nativeXiRootSynthesis rho) (nativeXiRootSynthesis_bijective rho)

/-- Actual original cohomology classes exhaust the whole native root block. -/
def meyerNativeRootEquiv (rho : XiDivisorSupport) :
    LinearMap.range (meyerFiniteHedenmalmSynthesis {rho}) ≃ₗ[ℂ] NativeXiRootBlock rho :=
  (meyerFiniteHedenmalmCoordinates {rho}).symm.trans (nativeXiRootCoordinates rho)

theorem meyerNativeRootEquiv_apply (rho : XiDivisorSupport)
    (u : LinearMap.range (meyerFiniteHedenmalmSynthesis {rho})) :
    (meyerNativeRootEquiv rho u).val = meyerFiniteUniformEmbedding {rho} u := rfl

/-- The whole-space comparison is also onto the full Hilbert source block. -/
theorem nativeSourceRootMap_bijective (rho : XiDivisorSupport) :
    Function.Bijective (nativeSourceRootMap rho) := by
  refine ⟨nativeSourceRootMap_injective rho, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_nativeXiRootBlock, finrank_thetaRootBlock_at_XiSupport])).mp
      (nativeSourceRootMap_injective rho)

def nativeSourceRootEquiv (rho : XiDivisorSupport) :
    NativeXiRootBlock rho ≃ₗ[ℂ] ThetaRootBlock (thetaSpectrumOfXiSupport rho) :=
  LinearEquiv.ofBijective (nativeSourceRootMap rho) (nativeSourceRootMap_bijective rho)

end RHTower.PaperThetaEndpoint
