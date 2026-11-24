import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.SectorEntries
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.SectorMinor

/-! # A common finite splitting doubles both independent response families -/
open Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "P" => (E × ℂ) × ℂ

private def entries (k : I) (w : I→List E) (j m : Bool) (u : ℂ) (F : I→P→ℂ) : Matrix I I ℂ :=
  of fun i l => sectorEntry k w j m i u (F l)

private def scale (k : I) (u : ℂ) : I⊕I → ℂ := Sum.elim (fun _ => 1) (fun i => if i=k then u else 1)

private theorem normalized_matrix (k : I) (w : I→List E) (j : Bool) (u : ℂ) (F : Bool→I→P→ℂ) :
    fromBlocks (entries k w j true u (F false)) (entries k w j true u (F true))
      (entries k w j false u (F false)) (entries k w j false u (F true)) =
      diagonal (scale k u)*readings (.inl k) (nextWords k w) j (Sum.elim (F false) (F true)) := by
  ext i l
  rcases i with i|i <;> rcases l with l|l <;> by_cases hi : i=k <;>
    simp [entries,sectorEntry,scale,readings,nextWords,diagonal_mul,fromBlocks,hi]

/-- Nonzero even and odd response minors of the old chain give nonzero
response minors of the doubled chain for all sufficiently large integer splittings. -/
theorem enlarged_minor (k : I) (w : I→List E) (f : I→E × ℂ → ℂ)
    (e : Bool→I→P × ℂ → ℂ) (ha : ∀ b l, AnalyticAt ℂ (e b l) 0)
    (hπ : ∀ b l, ∀ᶠ p : P in 𝓝 0, e b l (p,0)=f l (projectField b p))
    (hdet : ∀ m, (readings k w m f).det≠0) (j : Bool) :
    ∀ᶠ n : ℕ in atTop, (readings (.inl k) (nextWords k w) j
      (Sum.elim (fun l => energy false (e false l) n) (fun l => energy true (e true l) n))).det≠0 := by
  let A (m : Bool) : Matrix I I ℂ := of fun i l => weight k j m i*readings k w m f i l
  let Q (m b : Bool) (n : ℕ) := entries k w j m (inverseHeight n) (fun l => energy b (e b l) n)
  let T (n : ℕ) := fromBlocks (Q true false n) (Q true true n) (Q false false n) (Q false true n)
  let L := fromBlocks (A true) (A true) (A false) (-(A false))
  have hentry (m b : Bool) (i l : I) : Tendsto (fun n => Q m b n i l) atTop (𝓝 (sign b^order m*A m i l)) := by
    simpa only [A,Q,entries,of_apply,readings,mul_assoc] using
      sectorEntry_limit k w j m b i (f l) (e b l) (ha b l) (hπ b l)
  have ht : Tendsto T atTop (𝓝 L) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro l
    rcases i with i|i <;> rcases l with l|l
    · simpa [T,L,fromBlocks,sign,order] using hentry true false i l
    · simpa [T,L,fromBlocks,sign,order] using hentry true true i l
    · simpa [T,L,fromBlocks,sign,order] using hentry false false i l
    · simpa [T,L,fromBlocks,sign,order] using hentry false true i l
  have hn (m : Bool) : (A m).det≠0 := weighted_det_ne _ (hdet m) _ (weight_ne k j m)
  have hL : L.det≠0 := by
    rw [show L.det=_ from sector_minor (A true) (A false)]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hn true)) (hn false)
  have hc : Continuous (fun X : Matrix (I⊕I) (I⊕I) ℂ => X.det) := continuous_id.matrix_det
  filter_upwards [(hc.continuousAt.tendsto.comp ht).eventually_ne hL] with n h
  have he := normalized_matrix k w j (inverseHeight n) (fun b l => energy b (e b l) n)
  change (T n).det≠0 at h
  change T n=_ at he
  rw [he,det_mul] at h
  exact (mul_ne_zero_iff.mp h).2

#print axioms enlarged_minor
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
