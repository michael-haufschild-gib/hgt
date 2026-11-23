import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.DisjointBoxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.UniformMarks

/-! # More than one physical gate per bond at every fixed positive date -/
open MeasureTheory Filter Set Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal
noncomputable section

/-- On any positive compact time interval, a deterministic positive
fraction of the wires must participate in a nonmerging gate. -/
theorem gaussian_positive_mark_density {a T : ℝ} (ha : 0<a) :
    ∃ d>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
      ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖ ≤ 1/4 →
      d*(n+1:ℕ) ≤ ((marked (circuitWord C)).card:ℝ) := by
  classical
  let δ := 1/(1024*(1+|T|))
  have hden : 0 < (1024:ℝ)*(1+|T|) := by positivity
  have hδ : 0<δ := one_div_pos.mpr hden
  let z₀ := π/(2*sqrt 2)
  have hz₀ : 0<z₀ := by dsimp [z₀]; positivity
  obtain ⟨B,hB⟩ := exists_nat_gt ((z₀/a)/δ)
  choose p hp hfreq using fun j : Fin (B+1) => good_boxes_density (j.val*δ) hδ
  let m := univ.inf' (univ_nonempty : (univ : Finset (Fin (B+1))).Nonempty) p
  have hm : 0<m := (lt_inf'_iff _).mpr (fun j _ => hp j)
  refine ⟨m/5,by positivity,?_⟩
  filter_upwards [ae_all_iff.mpr hfreq] with ω hw
  choose K hK using fun j => eventually_atTop.mp (hw j)
  filter_upwards [eventually_ge_atTop (4*(univ.sup K)+20)] with n hn
  intro t ht C z hz hfit
  let q := z₀/t
  have ht₀ := ha.trans_le ht.1
  have hq : 0<q := div_pos hz₀ ht₀
  have hq' : q/δ<(B:ℝ) :=
    (div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hz₀.le ha ht.1) hδ.le).trans_lt hB
  let j : Fin (B+1) := ⟨⌊q/δ⌋₊,by
    have hi := (Nat.floor_le (div_nonneg hq.le hδ.le)).trans_lt hq'
    have h : ⌊q/δ⌋₊<B := by exact_mod_cast hi
    omega⟩
  have hjlo : (j.val:ℝ)*δ ≤ q := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hq.le hδ.le))
  have hjhi : q < ((j.val:ℝ)+1)*δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (q/δ))
  have herr : |(j.val:ℝ)*δ-q|≤δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hjlo)]
    linarith only [hjhi]
  have heq : (q*sqrt 2)*t=π/2 := by
    dsimp only [q,z₀]
    field_simp [ht₀.ne',(sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne']
  have hsmall : |t| * (63*(2*δ))≤1/8 := by
    rw [abs_of_pos ht₀]
    have hbound : t≤1+|T| := by linarith only [ht.2,le_abs_self T]
    have hδbound := mul_le_mul_of_nonneg_right hbound hδ.le
    have hc : (1+|T|)*δ=1/1024 := by dsimp only [δ]; field_simp [show 1+|T|≠0 by positivity]
    rw [hc] at hδbound
    linarith only [hδbound]
  have hcount := count_good_boxes herr heq hsmall C z hz hfit
  have hk := le_sup (f:=K) (mem_univ j)
  have hfr := hK j ((n+1)/4) (by omega)
  have hnum : ((n+1:ℕ):ℝ) ≤ 5*((((n+1)/4:ℕ):ℝ)) := by exact_mod_cast (by omega : n+1 ≤ 5*((n+1)/4))
  calc (m/5)*((n+1:ℕ):ℝ) ≤ m*((((n+1)/4:ℕ):ℝ)) := by
         linarith only [mul_le_mul_of_nonneg_left hnum hm.le]
       _ ≤ p j*((((n+1)/4:ℕ):ℝ)) := mul_le_mul_of_nonneg_right (inf'_le p (mem_univ j)) (Nat.cast_nonneg _)
       _ ≤ _ := hfr.trans (Nat.cast_le.mpr hcount)

/-- The physical gate density exceeds one by a fixed positive amount,
uniformly on the interval and for one draw of the infinite chain. -/
theorem gaussian_strict_spanning_floor {a T : ℝ} (ha : 0<a) :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ∈ Icc a T →
      ∀ s : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1+c)*(n+1:ℕ) < (s:ℝ) := by
  obtain ⟨d,hd,hm⟩ := gaussian_positive_mark_density (T:=T) ha
  have he : (1/4:ℝ)<sqrt 2 := (by norm_num : (1/4:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))
  refine ⟨d/4,by positivity,?_⟩
  filter_upwards [hm,gaussian_uniform_marked_floor (T:=T) ha (show 0<d/4 by positivity)
    (by norm_num : (0:ℝ)≤1/4) he] with ω hω hf
  filter_upwards [hω,hf] with n hn hn'
  intro t ht s hs
  let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  have habs : HasProjectiveCircuitApproximation (n+2) (1/4) s (unitaryEvolution H.val |t|) := by
    rcases le_total 0 t with h|h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_nonpos h]; exact hs.neg_time H
  obtain ⟨z,hz,C,hC,hfit⟩ := habs
  have h₁ := hn |t| ht C z hz hfit
  have h₂ := hn' |t| ht C z hz hfit
  have hs' : (C.gateCount:ℝ) ≤ s := Nat.cast_le.mpr hC
  linarith only [h₁,h₂,hs']

#print axioms gaussian_positive_mark_density
#print axioms gaussian_strict_spanning_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
