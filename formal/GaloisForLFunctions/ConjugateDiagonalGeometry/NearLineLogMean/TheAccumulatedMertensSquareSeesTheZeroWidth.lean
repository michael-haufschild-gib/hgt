import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PoissonEnergyOfTheMertensPrefixes

/-!
# The accumulated Mertens square sees the zero width

The boundary square of a truncated Poisson Gram form can be discarded.
In every upper half-octave some cutoff recovers it within a constant
factor of the accumulated positive mass. Thus the latter detects the
zero width even when bounded only at arbitrarily sparse cutoffs.
-/

noncomputable section
open Finset Filter
open scoped Topology
open _root_.RHTower GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Increment of the accumulated mean square in reciprocal length. -/
def mertensSquareCell (k : ℕ) : ℝ := ((k:ℝ)⁻¹-((k:ℝ)+1)⁻¹)*‖mobiusMertensPartialSum k‖^2

/-- Accumulated Mertens square with the terminal Poisson term removed. -/
def mertensSquareMass (N : ℕ) := ∑ k ∈ Icc 1 N, mertensSquareCell k

private theorem cell_nn {k : ℕ} (hk : 1 ≤ k) : 0 ≤ mertensSquareCell k :=
  mul_nonneg (sub_nonneg.mpr (inv_anti₀ (Nat.cast_pos.mpr hk) (le_add_of_nonneg_right zero_le_one))) (sq_nonneg _)

theorem mertens_square_mass_mono : Monotone mertensSquareMass := fun _ _ h =>
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ hk _ => cell_nn (mem_Icc.mp hk).1

private theorem mass_nn (N : ℕ) : 0 ≤ mertensSquareMass N :=
  sum_nonneg fun _ hk => cell_nn (mem_Icc.mp hk).1

private theorem gram_decomposition {k : ℕ} (hk : 1 ≤ k) :
    mertensPoissonGram k = ((k:ℝ)+1)*mertensSquareCell k + mertensSquareMass (k-1) := by
  rw [mertens_gram_prefix_squares hk]
  congr 1
  dsimp only [mertensSquareCell]
  have hp := (Nat.cast_pos (α:=ℝ)).mpr hk
  field_simp [hp.ne',(by positivity : (k:ℝ)+1 ≠ 0)] <;> ring

/-- An upper-half cutoff has its complete Poisson cost at most five
times the cumulative square mass at the terminal cutoff. -/
theorem half_octave_mertens_square_selection {N : ℕ} (hN : 1 ≤ N) :
    ∃ k ∈ Ioc (N/2) N, mertensPoissonGram k ≤ 5*mertensSquareMass N := by
  let S := Ioc (N/2) N
  have hn := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have hcard : (N:ℝ) ≤ 2*(S.card:ℝ) := by
    dsimp only [S]
    rw [Nat.card_Ioc]
    exact_mod_cast (show N ≤ 2*(N-N/2) by omega)
  have hsubset : S ⊆ Icc 1 N := fun k hk => by
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hk
    exact mem_Icc.mpr ⟨by omega,hr⟩
  have small : (∑ k ∈ S, mertensSquareCell k) ≤ mertensSquareMass N :=
    sum_le_sum_of_subset_of_nonneg hsubset fun _ hk _ => cell_nn (mem_Icc.mp hk).1
  have mass := mass_nn N
  have hsum : (∑ k ∈ S, ((N:ℝ)+1)*mertensSquareCell k) ≤ ∑ _k ∈ S, 4*mertensSquareMass N := by
    rw [←mul_sum,sum_const,nsmul_eq_mul]
    have hfac : (N:ℝ)+1 ≤ 4*(S.card:ℝ) := by linarith only [hn,hcard]
    exact (mul_le_mul (le_refl _) small (sum_nonneg fun _ hk => cell_nn (mem_Icc.mp (hsubset hk)).1)
      (by positivity)).trans ((mul_le_mul_of_nonneg_right hfac mass).trans_eq (by ring))
  have ne : S.Nonempty := ⟨N,mem_Ioc.mpr ⟨by omega,le_rfl⟩⟩
  obtain ⟨k,hk,h⟩ := exists_le_of_sum_le ne hsum
  obtain ⟨kp,kN⟩ := mem_Icc.mp (hsubset hk)
  refine ⟨k,hk,?_⟩
  rw [gram_decomposition kp]
  have hcell := mul_le_mul_of_nonneg_right (add_le_add_right (Nat.cast_le.mpr kN : (k:ℝ) ≤ N) 1) (cell_nn kp)
  have hmass := mertens_square_mass_mono ((Nat.sub_le k 1).trans kN)
  linarith only [hcell,h,hmass]

/-- Cofinal control of the accumulated square alone bounds the actual
zero width, without assumptions on the spacing of the cutoffs. -/
theorem width_le_of_sparse_mertens_square_mass {b : ℝ} (hb : 0 ≤ b)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ N : ℕ in atTop, mertensSquareMass N ≤ C*(N:ℝ)^(2*b)) :
    zetaZeroWidth ≤ b := by
  obtain ⟨C,hC,hh⟩ := h
  apply width_le_of_cofinal_mertens_gram hb
  refine ⟨5*C*2^(2*b),by positivity,frequently_atTop.mpr fun n => ?_⟩
  obtain ⟨N,hN,hbound⟩ := frequently_atTop.mp hh (2*n+1)
  obtain ⟨k,hk,hcost⟩ := half_octave_mertens_square_selection (N:=N) (by omega)
  have hkn := (mem_Ioc.mp hk).1
  have h2 : (N:ℝ) ≤ 2*k := by exact_mod_cast (show N ≤ 2*k by omega)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) h2 (mul_nonneg (by norm_num) hb)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg k)] at hpow
  refine ⟨k,by omega,hcost.trans ?_⟩
  calc 5*mertensSquareMass N ≤ 5*(C*(N:ℝ)^(2*b)) := by linarith only [hbound]
       _ ≤ 5*(C*(2^(2*b)*(k:ℝ)^(2*b))) := by gcongr
       _ = _ := by ring

/-- Every large cutoff exceeds each subcritical power with arbitrarily
large fixed multiplier. -/
theorem eventually_large_mertens_square_mass {b : ℝ} (hb : 0 ≤ b) (h : b < zetaZeroWidth)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, C*(N:ℝ)^(2*b) < mertensSquareMass N := by
  by_contra hh
  have hf : ∃ᶠ N : ℕ in atTop, mertensSquareMass N ≤ C*(N:ℝ)^(2*b) := by
    simpa only [not_eventually,not_lt] using hh
  exact h.not_ge (width_le_of_sparse_mertens_square_mass hb ⟨C,hC,hf⟩)

/-- Every supercritical power bounds the accumulated square mass. -/
theorem mertens_square_mass_upper {b : ℝ} (h : zetaZeroWidth < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, mertensSquareMass N ≤ C*((N:ℝ)+1)^(2*b) := by
  obtain ⟨C,hC,hbound⟩ := mertens_gram_upper_power h
  refine ⟨C,hC,fun N => ?_⟩
  have hh := hbound (N+1)
  rw [gram_decomposition (Nat.succ_pos N),Nat.add_sub_cancel,Nat.cast_succ] at hh
  linarith only [hh,mul_nonneg (by positivity : 0 ≤ (N:ℝ)+1+1) (cell_nn (Nat.succ_pos N))]

#print axioms half_octave_mertens_square_selection
#print axioms width_le_of_sparse_mertens_square_mass
#print axioms eventually_large_mertens_square_mass
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
