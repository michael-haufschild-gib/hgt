import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.LocalSublevel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.WindingForecast
import Mathlib.Data.Fintype.Lattice

/-! # Short-window probability for an actual scalar entry under a Gaussian field -/

open Matrix Set Real Filter MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
open PrecisionReturns
open SharpOccupation (physicalArc physicalArc_spec)
noncomputable section

/-- A field chosen from a standard Gaussian makes a genuine entry in a
narrow forecast window with probability at most linear in its D²th root,
on an energy-bounded part of the field line. All exterior origins are tested
at once. The constant may depend on the frozen background and the forecast. -/
theorem pencil_entry_window {N : ℕ} (A Z : Register N)
    (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian) (hP : ∀ b : ℝ, b≠0 → (gapPencil A Z b).det≠0)
    (T L ε : ℝ) (hT : 0<T) (hL : 0<L) (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let D := (2^N:ℕ)^2
    let H (y : ℝ) : selfAdjoint (Register N) := ⟨A+(y:ℂ) • Z,(hH y).isSelfAdjoint⟩
    ∃ c> (0:ℝ), ∃ K : ℝ, ∀ r∈Ioc (0:ℝ) 1,
      (gaussianReal 0 1).real {y : ℝ | (∀ i, |(hH y).eigenvalues i|≤L) ∧
        ∃ a> (0:ℝ), ε<orbitCircuitDistance (H y) 0 a ∧ |firstVisit (H y) a 0 ε-T|<c*r^D}≤K*r := by
  classical
  intro D H
  let x := physicalArc ε
  have hx := (physicalArc_spec he.1 he.2).1
  let F := windingBox T (2*L)
  have hF := winding_forecast hT (show 0≤2*L by positivity)
    (show x∈Icc (0:ℝ) 1 from ⟨hx.1.le,hx.2.le.trans (by norm_num)⟩)
  let b (n : ℤ) := (2*π)*((n:ℝ)+x)/T
  have hn (n : ℤ) : b n≠0 := by
    apply div_ne_zero _ hT.ne'
    apply mul_ne_zero two_pi_pos.ne'
    by_cases hz : 0≤n
    · exact (add_pos_of_nonneg_of_pos (by exact_mod_cast hz : (0:ℝ)≤n) hx.1).ne'
    · have h : (n:ℝ)≤-1 := by exact_mod_cast (show n≤-1 by omega)
      linarith only [h,hx.2]
  choose d hd hdet using fun n : F => gap_small_window A Z hH (b n.val) L (hP _ (hn _))
  letI : Nonempty F := ⟨⟨0,Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg _),Nat.cast_nonneg _⟩⟩⟩
  obtain ⟨n₀,hmin⟩ := Finite.exists_min d
  let u := d n₀
  have hu : 0<u := hd n₀
  let Q := 2*L/T
  have hQ : 0<Q := div_pos (mul_pos zero_lt_two hL) hT
  let c := min 1 (u/Q)
  have hc : 0<c := lt_min zero_lt_one (div_pos hu hQ)
  have hscale : Q*c≤u := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 (u/Q)) hQ.le
    simpa only [mul_div_cancel₀ _ hQ.ne'] using h
  have hcard : Fintype.card (Fin N → Bool)^2=D := by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,D]
  refine ⟨c,hc,(F.card:ℝ)*(2*D),fun r hr => ?_⟩
  let B (n : F) := {y : ℝ | (∀ i, |(hH y).eigenvalues i|≤L) ∧
    ∃ i j, |b n.val-((hH y).eigenvalues i-(hH y).eigenvalues j)|<d n*r^D}
  have hmass (n : F) : (gaussianReal 0 1).real (B n)≤2*D*r := by
    simpa only [B,hcard] using hdet n r hr
  calc
    _ ≤ (gaussianReal 0 1).real (⋃ n : F, B n) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro y ⟨hE,a,ha,hout,hwindow⟩
      let v := firstVisit (H y) a 0 ε
      obtain ⟨hv,i,j,n,_,hgap⟩ := first_entry_gap (H y) ha he.1 he.2 hout
      let g := (hH y).eigenvalues i-(hH y).eigenvalues j
      have hg : |g|≤2*L := (abs_sub _ _).trans (by linarith only [hE i,hE j])
      have hvT : |v-T|≤1 := hwindow.le.trans (mul_le_one₀ (min_le_left ..) (pow_nonneg hr.1.le _) (pow_le_one₀ hr.1.le hr.2))
      obtain ⟨hnF,herr⟩ := hF v g n hv hvT hg hgap
      let m : F := ⟨n,hnF⟩
      refine mem_iUnion.mpr ⟨m,hE,i,j,herr.trans_lt ?_⟩
      calc
        Q*|v-T| < Q*(c*r^D) := mul_lt_mul_of_pos_left hwindow hQ
        _ = (Q*c)*r^D := (mul_assoc ..).symm
        _ ≤ d m*r^D := mul_le_mul_of_nonneg_right (hscale.trans (hmin m)) (pow_nonneg hr.1.le _)
    _ ≤ _ := by
      refine (measureReal_iUnion_fintype_le B).trans ((Finset.sum_le_sum fun n _ => hmass n).trans_eq ?_)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_assoc]

#print axioms pencil_entry_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
