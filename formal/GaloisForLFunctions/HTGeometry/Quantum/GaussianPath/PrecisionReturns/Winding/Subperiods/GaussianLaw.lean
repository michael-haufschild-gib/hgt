import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.WireCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.HalfSpectrum

/-! # Full physical support before the first low-budget return -/

open Set Real Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- At inverse-precision subdivisions of the distinguished return, every
fit at the original tolerance touches the entire register in every basis.
Coprime multiples share this conclusion as long as their initial winding
error remains within a quarter turn. -/
theorem gaussian_full_support_subperiods :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A > (0:ℝ), ∀ a > (0:ℝ), ∀ s : ℕ, s+1<N →
        ∀ᶠ ε in 𝓝[>] (0:ℝ),
          let v := firstVisit H a s ε
          let R := physicalArc (A*ε)
          R ≤ 1/4 ∧ ε*(⌈1/ε⌉₊:ℝ) ≤ 5/4 ∧
          ∀ d j : ℕ, 1/ε ≤ (d:ℝ) → ε*d ≤ 5/4 → d.Coprime j → (j:ℝ)*R ≤ 1/4 →
            ∀ (V : unitaryGroup (Fin N→Bool) ℂ) (C : TwoQubitCircuit N) (c : ℂ),
              ‖V.val*unitaryEvolution H.val ((j:ℝ)/d*v)*star V.val-c • C.eval.val‖ ≤ ε →
                C.touchedSites=Finset.univ := by
  filter_upwards [CollisionRank.gaussian_half_spectrum_residues] with ω hh k
  intro N H
  obtain ⟨A,hA,h⟩ := hh k
  refine ⟨A,hA,?_⟩
  intro a ha s hs
  have hsmall := Ioo_mem_nhdsGT (show 0 < (1/2:ℝ)/A by positivity)
  filter_upwards [h a ha s hs,hsmall,Ioo_mem_nhdsGT (show (0:ℝ)<1/4 by norm_num)] with ε hz hε hq
  intro v R
  have hAε : A*ε < 1/2 := by simpa only [mul_comm A] using (lt_div_iff₀ hA).mp hε.2
  have hR := (ShortTimeProducts.physical_arc_bounds (mul_pos hA hε.1)
    (hAε.trans_le ((by norm_num : (1/2:ℝ)≤1).trans (one_le_sqrt.mpr (by norm_num))))).2
  have hR' : R ≤ 1/4 := by change R≤A*ε/2 at hR; linarith only [hR,hAε]
  have hdense := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (one_div_nonneg.mpr hε.1.le)) hε.1
  have heq : ε*(1/ε+1)=1+ε := by field_simp [hε.1.ne']
  rw [heq] at hdense
  refine ⟨hR',by linarith only [hdense,hq.2],?_⟩
  intro d j hlo hhi hj hturn V C c hfit
  have hd : 0<d := Nat.cast_pos.mp ((one_div_pos.mpr hε.1).trans_le hlo)
  obtain ⟨b,z,hb⟩ := hz.1
  have hc := hz.2 b z hb d hlo
  have he : 2*ε < 4*(1-(j:ℝ)*R)/d := (lt_div_iff₀ (Nat.cast_pos.mpr hd)).mpr (by linarith only [hhi,hturn])
  have hcount := wire_count H hb (hR'.trans_lt (by norm_num)) hd hj he V C c hfit
  by_contra hn
  have hc' := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hn)
  rw [Finset.card_univ,Fintype.card_fin] at hc'
  have hh' : C.touchedSites.card ≤ k+2 := by dsimp only [N] at hc'; omega
  exact (Nat.lt_succ_of_le hc).not_ge (hcount.trans (Nat.pow_le_pow_right (by decide) hh'))

/-- In particular the actual first visit, divided by the ceiling of inverse
precision, has no fit omitting even one wire. No choice of spectral basis
lowers the required support. -/
theorem gaussian_inverse_precision_subperiod :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ∀ s : ℕ, s+1<N → ∀ᶠ ε in 𝓝[>] (0:ℝ),
        let t := firstVisit H a s ε/(⌈1/ε⌉₊:ℝ)
        ∀ (V : unitaryGroup (Fin N→Bool) ℂ) (C : TwoQubitCircuit N) (c : ℂ),
          ‖V.val*unitaryEvolution H.val t*star V.val-c • C.eval.val‖ ≤ ε →
            C.touchedSites=Finset.univ ∧ N ≤ 2*C.gateCount := by
  filter_upwards [gaussian_full_support_subperiods] with ω hh k
  intro N H a ha s hs
  obtain ⟨A,_,hh⟩ := hh k
  filter_upwards [hh a ha s hs] with ε he
  intro t V C c hfit
  have h := he.2.2 ⌈1/ε⌉₊ 1 (Nat.le_ceil _) he.2.1 (Nat.coprime_one_right _) (by simpa only [Nat.cast_one,one_mul] using he.1) V C c
  have ht : (1:ℝ)/(⌈1/ε⌉₊:ℝ)*firstVisit H a s ε=t := by dsimp only [t]; ring
  rw [Nat.cast_one,ht] at h
  have hsites := h hfit
  refine ⟨hsites,?_⟩
  simpa only [hsites,Finset.card_univ,Fintype.card_fin] using C.card_touchedSites_le

#print axioms gaussian_full_support_subperiods
#print axioms gaussian_inverse_precision_subperiod
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
