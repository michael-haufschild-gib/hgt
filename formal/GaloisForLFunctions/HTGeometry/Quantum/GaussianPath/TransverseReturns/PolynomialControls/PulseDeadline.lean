import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.SingleDirection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.HighOrderSquare
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.FirstWait

/-! # High-order quadratic pulses at genuine physical return dates -/
open Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
open PrecisionReturns
noncomputable section
open private compose_error from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.FirstWait

/-- The quadratic pencil has one independently correctable phase. At
contact order p=j+2 it costs a factor m on that phase and m^p on each
of the D−3 remaining phases. The visit lies beyond the chosen origin. -/
theorem high_order_path_deadline {n : ℕ} (u : PathShell n) (a b c : Fin (n+2) → Bool) (j : ℕ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let E := H.2.isHermitian.eigenvalues
    let S := 3^j*(Fintype.card (PathLabel n)+1)^2*9
    let D : ℕ := 2^(n+2)
    let p := j+2
    E a < E b → E c ≠ E a → E c ≠ E b →
    ∃ B>(0:ℝ), ∀ A : ℝ, ∃ T>(0:ℝ), ∀ m : ℕ, 0 < m →
      ∃ t : ℝ, A < t ∧ t ≤ T*(m:ℝ)^(p*(D-3)+1) ∧
        HasProjectiveCircuitApproximation (n+2) (B/(m:ℝ)^p) S (unitaryEvolution H.val t) := by
  intro H E S D p hab hca hcb
  let z := (E a+E b)/2
  let F (i) := (E i-z)^2
  have hpin : F b=F a := by dsimp only [F,z]; ring
  have hg : F c-F a ≠ 0 := by
    rw [show F c-F a=(E c-E a)*(E c-E b) by dsimp only [F,z]; ring]
    exact mul_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hcb)
  let L := 2*π/|F c-F a|
  have hL : 0 < L := div_pos two_pi_pos (abs_pos.mpr hg)
  obtain ⟨C,hC,δ,hδ,hstep⟩ := high_order_square u z j
  obtain ⟨M,hM⟩ := exists_nat_gt (L/δ)
  have hM₀ : 0 < M := Nat.cast_pos.mp ((div_pos hL hδ).trans hM)
  have hM₁ : (1:ℝ) ≤ M := by exact_mod_cast hM₀
  refine ⟨2*π+C*L^p,by positivity,?_⟩
  intro A
  let P := 2*π/(E b-E a)
  have hP : 0 < P := div_pos two_pi_pos (sub_pos.mpr hab)
  obtain ⟨l,hl⟩ := exists_nat_gt (max A 0/P)
  let τ := (l:ℝ)*P
  have hτ : max A 0 < τ := (div_lt_iff₀ hP).mp hl
  have hτ₀ : 0 < τ := (le_max_right A 0).trans_lt hτ
  have hturn : τ*(E b-E a)/(2*π)=((l:ℤ):ℝ) := by
    dsimp only [τ,P]; push_cast; field_simp [(sub_pos.mpr hab).ne']
  refine ⟨τ*(M:ℝ),mul_pos hτ₀ (Nat.cast_pos.mpr hM₀),?_⟩
  intro m hm
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨q,hq,hQ,β,hβ,hwind⟩ := two_scale_pencil E F a b c
    (fun h => hab.ne (congrArg E h)) (fun h => hca (congrArg E h)) (fun h => hcb (congrArg E h))
    (l:ℤ) hturn hpin (sub_ne_zero.mp hg) (Nat.mul_pos hM₀ hm) (pow_pos hm p)
  rw [Nat.cast_mul] at hβ
  have hβ' : |β| ≤ L/(m:ℝ) := hβ.trans (div_le_div_of_nonneg_left hL.le hm'
    (le_mul_of_one_le_left hm'.le hM₁))
  have hβδ : |β| ≤ δ := by
    apply hβ.trans
    apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hM₀) hm')).mpr
    calc
      L ≤ (M:ℝ)*δ := ((div_lt_iff₀ hδ).mp hM).le
      _ ≤ ((M:ℝ)*δ)*m := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) hδ.le) hm₁
      _ = _ := by ring
  have hcard : Fintype.card (Fin (n+2) → Bool)=D := by simp [D]
  rw [hcard,←pow_mul,mul_assoc,←pow_succ'] at hQ
  have hQ' : (q:ℝ) ≤ (M:ℝ)*(m:ℝ)^(p*(D-3)+1) := by exact_mod_cast hQ
  let t := (q:ℝ)*τ
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨t,(le_max_left A 0).trans_lt (hτ.trans_le (le_mul_of_one_le_left hτ₀.le hq₁)),?_,?_⟩
  · calc
      _ ≤ ((M:ℝ)*(m:ℝ)^(p*(D-3)+1))*τ := mul_le_mul_of_nonneg_right hQ' hτ₀.le
      _ = _ := by ring
  · have hwind' := quadratic_close H.val H.2.isHermitian z a
        (by positivity : 0 ≤ 1/(m:ℝ)^p) (by simpa only [Nat.cast_pow] using hwind)
    obtain ⟨v,hv,C',hgates,hfit⟩ := compose_error hwind' (hstep β hβδ)
    refine ⟨v,hv,C',hgates,hfit.trans ?_⟩
    calc
      _ ≤ 2*π*(1/(m:ℝ)^p)+C*(L/(m:ℝ))^p := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hβ' _) hC.le)
      _ = _ := by rw [div_pow]; ring

#print axioms high_order_path_deadline
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
