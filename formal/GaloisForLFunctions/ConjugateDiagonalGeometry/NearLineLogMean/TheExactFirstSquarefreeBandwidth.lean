import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheFirstNeighborsInTheLogWindowSpectrum

/-!
# The exact end of the diagonal band

The first occupied gap in a sufficiently long squarefree section is the
logarithmic spacing of its last pair of consecutive squarefree integers.
All larger bandwidth intervals contain interference. At the first gap the
two coefficients have a nonzero signed product.
-/
noncomputable section
open Finset Complex Filter
open scoped Topology
open _root_.RHTower (mobiusRealCoefficient sum_Icc_eq_sum_range_shift)
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- Length of the last occupied neighbor gap in the squarefree section. -/
def firstSquarefreeBandwidth (N : ℕ) := adjacentLogGap (lastSquarefreeNeighbor N)

/-- The literal mass on the diagonal of a critical Möbius section. -/
def squarefreeWindowMass (N : ℕ) := ∑ j∈Icc 1 N,mobiusRealCoefficient j^2/j

private theorem diagonal_mass (N : ℕ) :
    (∑ j∈range N, ‖(coeff (j+1):ℂ)‖^2)=squarefreeWindowMass N := by
  rw [squarefreeWindowMass,sum_Icc_eq_sum_range_shift]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem vanishing_gram {i : ℕ} (h : ¬(Squarefree i ∧ Squarefree (i+1))) :
    gram (coeff (i+1):ℂ) (coeff i:ℂ)=0 := by
  simp only [gram,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re]
  by_cases hi : Squarefree i
  · have hj : ¬Squarefree (i+1) := fun hj => h ⟨hi,hj⟩
    simp [coeff,mobiusRealCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hj]
  · simp [coeff,mobiusRealCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi]

private theorem below_last_edge {N : ℕ} (hN : 2≤N) (hhalf : N≤2*lastSquarefreeNeighbor N)
    {d : ℝ} (hd : 0≤d) (hcut : d≤firstSquarefreeBandwidth N) :
    bandEnergy N d=d*squarefreeWindowMass N := by
  rcases N with _|M
  · omega
  let k := lastSquarefreeNeighbor (M+1)
  obtain ⟨hk,hkN,_,_,hmax⟩ := last_squarefree_neighbor_spec hN
  change d≤adjacentLogGap k at hcut
  have hk' : 0<(k:ℝ) := Nat.cast_pos.mpr hk
  have hlim := (le_div_iff₀ hk').mp (hcut.trans (adjacent_log_gap_bounds hk).2)
  have hwidth : d*((M+1:ℕ):ℝ)≤2 := by
    have hhalf' : ((M+1:ℕ):ℝ)≤2*(k:ℝ) := by exact_mod_cast hhalf
    calc _ ≤ d*(2*(k:ℝ)) := mul_le_mul_of_nonneg_left hhalf' hd
         _ = 2*(d*(k:ℝ)) := by ring
         _ ≤ 2 := by linarith only [hlim]
  change energy (fun n => (coeff n:ℂ)) (M+1) d=_
  rw [log_window_adjacent_band _ _ hd hwidth,diagonal_mass]
  suffices hh : (∑ j∈range M,gram (coeff (j+2):ℂ) (coeff (j+1):ℂ)*
      max (d-adjacentLogGap (j+1)) 0)=0 by rw [hh,mul_zero,add_zero]
  apply sum_eq_zero
  intro j hj
  by_cases hocc : Squarefree (j+1) ∧ Squarefree (j+2)
  · have hjk : j+1≤k := hmax (j+1) (by omega) (by have := mem_range.mp hj;omega) hocc.1 hocc.2
    have hgap : adjacentLogGap k≤adjacentLogGap (j+1) := by
      rcases eq_or_lt_of_le hjk with he|he
      · rw [he]
      · exact (adjacent_log_gap_strict (by omega) he).le
    rw [max_eq_right (sub_nonpos.mpr (hcut.trans hgap)),mul_zero]
  · rw [vanishing_gram hocc,zero_mul]

/-- Whenever the last pair lies in the upper half of the prefix, its spacing
is exactly the largest bandwidth through which all energies are diagonal. -/
theorem exact_squarefree_diagonal_interval {N : ℕ} (hN : 2≤N) (hhalf : N≤2*lastSquarefreeNeighbor N)
    (b : ℝ) :
    (∀ d : ℝ,0≤d → d≤b → bandEnergy N d=d*squarefreeWindowMass N) ↔
      b≤firstSquarefreeBandwidth N := by
  refine ⟨fun h => ?_,fun hb d hd hdb => below_last_edge hN hhalf hd (hdb.trans hb)⟩
  by_contra! hlt
  let k := lastSquarefreeNeighbor N
  let x := firstSquarefreeBandwidth N
  obtain ⟨hk,hkN,hs,ht,_⟩ := last_squarefree_neighbor_spec hN
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hx : 0<x := (by positivity : 0<1/((k:ℝ)+1)).trans_le (adjacent_log_gap_bounds hk).1
  let δ := min (min x (b-x)) ((N:ℝ)^2)⁻¹
  have hδ : 0<δ := lt_min (lt_min hx (sub_pos.mpr hlt)) (inv_pos.mpr (sq_pos_of_pos hn))
  have hδx : δ≤x := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ≤b-x := (min_le_left _ _).trans (min_le_right _ _)
  have hcp : (k+1).Coprime k := by rw [Nat.add_comm k 1,Nat.coprime_add_self_left];simp
  have hnon := (ratio_readout_ne_zero_iff (N:=N) (a:=k+1) (b:=k)
    (mem_Icc.mpr ⟨by omega,by omega⟩) (mem_Icc.mpr ⟨hk,hkN.le⟩) hcp (by omega)
    hδ (min_le_right _ _)).mpr ⟨ht,hs⟩
  apply hnon
  change (bandEnergy N (x+δ)-2*bandEnergy N x+bandEnergy N (x-δ))/δ=0
  rw [h (x+δ) (add_nonneg hx.le hδ.le) (by linarith only [hδb]),h x hx.le hlt.le,
    h (x-δ) (sub_nonneg.mpr hδx) ((sub_le_self x hδ.le).trans hlt.le)]
  ring

/-- The exact last-neighbor law holds for every sufficiently large cutoff,
uniformly in the bandwidth being tested. -/
theorem eventually_exact_squarefree_diagonal_interval :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℝ,
      (∀ d : ℝ,0≤d → d≤b → bandEnergy N d=d*squarefreeWindowMass N) ↔
        b≤firstSquarefreeBandwidth N := by
  filter_upwards [eventually_ge_atTop 2,last_squarefree_neighbor_ratio.eventually_const_lt (by norm_num : (1/2:ℝ)<1)]
    with N hN hhalf
  apply exact_squarefree_diagonal_interval hN
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hh := (lt_div_iff₀ hn).mp hhalf
  exact_mod_cast (show (N:ℝ)≤2*(lastSquarefreeNeighbor N:ℝ) by linarith only [hh])

#print axioms exact_squarefree_diagonal_interval
#print axioms eventually_exact_squarefree_diagonal_interval
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
