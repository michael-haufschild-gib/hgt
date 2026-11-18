import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor
import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSavingsOnSignedDivisors

/-!
# The square conductor costs before ordinary prime rounding

Both logarithms use the same signed continuous prime degree. Proper powers,
the mesh and the original archimedean radius have separate uniform bounds.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticScatteringHolography SquareRootThreshold

/-- Adding back ordinary floor loss, both the ordinary generator and the
full excess over the radius are bounded by the width and mesh costs. -/
theorem square_cost_before_ordinary_floors : ∃ E : ℝ, 1 ≤ E ∧ ∀ {n m : ℕ}, 0 < n → 0 < m →
    let a := m • successorSquareTriple n
    let g := ((n:ℝ)+1)^zetaZeroWidth
    max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) +
      ordinaryFloorLoss a ≤ E*((m*g)^2+n*m) := by
  obtain ⟨A,hA,hdeg⟩ := successorSquare_degree_at_width
  obtain ⟨D,hD,hcontact⟩ := successorSquare_contact_degree
  obtain ⟨C,hC,hquad⟩ := ordinaryPrimeContact_sampling_error
  obtain ⟨H,hH,hwindow⟩ := successorSquare_window_bound
  obtain ⟨J,hJ,hjet⟩ := pole_balanced_ordinary_section_bound
  let E := 1+D+A+C*H+16*J
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hCH := mul_nonneg hC hH₀
  refine ⟨E,by unfold E; linarith only [hD,hA,hCH,hJ],fun {n m} hn hm => ?_⟩
  let d := successorSquareTriple n
  let a := m • d
  let g := ((n:ℝ)+1)^zetaZeroWidth
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution a
  have hX : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hg : 1 ≤ g := Real.one_le_rpow hX zetaZeroWidth_nonneg
  have hg₂ : 1 ≤ g^2 := one_le_pow₀ hg
  have hpow : ((n:ℝ)+1)^(2*zetaZeroWidth) = g^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul (zero_le_one.trans hX),Real.rpow_two]
  have hQ := hdeg n hn
  rw [hpow] at hQ
  have hp : ordinaryPrimeContact d ≤ (D+A)*g^2 := by
    linarith only [(abs_le.mp (hcontact hn)).2,(abs_le.mp hQ).1,mul_le_mul_of_nonneg_left hg₂ hD]
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hr : m ≤ r := successorSquare_resolution_ge n m
  have hr' : (m:ℝ) ≤ r := by exact_mod_cast hr
  have hdiv : (m:ℝ)^2*C/r ≤ C*m := by
    apply (div_le_iff₀ (hm'.trans_le hr')).mpr
    linarith only [mul_le_mul_of_nonneg_left hr' (mul_nonneg hC hm'.le)]
  have hroot := Real.sqrt_le_sqrt (hwindow hn)
  rw [Real.sqrt_sq (mul_nonneg hH₀ (Nat.cast_nonneg (α := ℝ) n))] at hroot
  have hsample := (abs_le.mp (hquad _ d (successorSquareTriple_mass n) m (hm.trans_le hr))).2
  have hcost := mul_le_mul hdiv hroot (Real.sqrt_nonneg _) (mul_nonneg hC hm'.le)
  have hbal : positivePoleDegree a = 0 := by
    change (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*(((m • d) i : ℤ) : ℝ)) = 0
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
    simp_rw [mul_left_comm _ (m:ℝ)]
    rw [← mul_sum,show (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*(d i : ℝ))=0 from positivePoleDegree_successorSquareTriple hn,mul_zero]
  have hv : (resolution d : ℝ) ≤ 4 := coefficientVariation_eq_resolution d ▸ successorSquareTriple_mass n
  have hr₁ : (r:ℝ) ≤ (m:ℝ)*4 := by
    unfold r a
    rw [resolution_smul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hv hm'.le
  have hr₂ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hr₁ 2) hJ
  have hj := hjet _ a hbal
  have hmg := mul_le_mul_of_nonneg_left hg₂ (sq_nonneg (m:ℝ))
  have h₁ : D+A+16*J ≤ E := by unfold E; linarith only [hCH]
  have h₂ : C*H ≤ E := by unfold E; linarith only [hD,hA,hJ]
  change Real.log (ordinaryPrimeGenerator a : ℝ)+ordinaryFloorLoss a-(m:ℝ)^2*ordinaryPrimeContact d ≤
    (m:ℝ)^2*C/r*Real.sqrt L at hsample
  change (m:ℝ)^2*C/r*Real.sqrt L ≤ (C*m)*(H*n) at hcost
  change Real.log (generator a : ℝ)-radius a ≤ Real.log (ordinaryPrimeGenerator a : ℝ)+J*(r:ℝ)^2 at hj
  change max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) +
    ordinaryFloorLoss a ≤ E*(((m:ℝ)*g)^2+(n:ℝ)*m)
  rw [← le_sub_iff_add_le,max_le_iff]
  have hbound := mul_le_mul_of_nonneg_left hp (sq_nonneg (m:ℝ))
  have hwidth := mul_le_mul_of_nonneg_right h₁ (sq_nonneg ((m:ℝ)*g))
  have hmesh := mul_le_mul_of_nonneg_right h₂ (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hm'.le)
  constructor
  · linarith only [hsample,hcost,hbound,hwidth,hmesh,mul_nonneg hJ (sq_nonneg ((m:ℝ)*g))]
  · linarith only [hsample,hcost,hj,hr₂,hbound,hwidth,hmesh,mul_le_mul_of_nonneg_left hmg hJ]

#print axioms square_cost_before_ordinary_floors

end GaloisForLFunctions.CountingHolography.Sections
