import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PinnedPencil
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PencilMetric
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.SquareWords
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # A quadratic-circuit return strictly beyond any prescribed origin -/
open Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

/-- A short spectral correction followed by a circuit approximation adds
their errors, since multiplication by a projective phase is isometric. -/
private theorem compose_error {n : ℕ} {U V : Register n} {δ ε : ℝ} {s : ℕ}
    (h : ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • V‖ ≤ δ)
    (hc : HasProjectiveCircuitApproximation n ε s V) :
    HasProjectiveCircuitApproximation n (δ+ε) s U := by
  obtain ⟨z,hz,he⟩ := h
  obtain ⟨c,hc,C,hC,herr⟩ := hc
  refine ⟨z*c,by rw [norm_mul,hz,one_mul,hc],C,hC,?_⟩
  calc
    _ ≤ ‖U-z • V‖+‖z • V-(z*c) • (C.eval : Register n)‖ := norm_sub_le _ _ _
    _ = ‖U-z • V‖+‖V-c • (C.eval : Register n)‖ := by rw [←smul_smul,←smul_sub,norm_smul,hz,one_mul]
    _ ≤ _ := add_le_add he herr

/-- For any three distinct energies with a positive first gap, a quadratic
gate budget admits a visit after A within τ m^(2D−5) at error B/m².
Both constants are independent of the requested precision. -/
theorem path_quadratic_deadline {n : ℕ} (u : PathShell n) (a b c : Fin (n+2) → Bool) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let E := H.2.isHermitian.eigenvalues
    let S := (Fintype.card (PathLabel n)+1)^2*9
    let D := 2^(n+2)
    E a < E b → E c ≠ E a → E c ≠ E b →
    ∃ B > (0:ℝ), ∀ A : ℝ, ∃ τ > (0:ℝ), ∀ m : ℕ, 0<m →
      ∃ t : ℝ, A<t ∧ t ≤ τ*(m:ℝ)^(2*D-5) ∧
        HasProjectiveCircuitApproximation (n+2) (B/(m:ℝ)^2) S (unitaryEvolution H.val t) := by
  intro H E S D hab hca hcb
  let z := (E a+E b)/2
  let F (i) := (E i-z)^2
  have hpin : F b=F a := by dsimp only [F,z]; ring
  have hg : F c-F a ≠ 0 := by
    rw [show F c-F a=(E c-E a)*(E c-E b) by dsimp only [F,z]; ring]
    exact mul_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hcb)
  let L := 2*π/|F c-F a|
  have hL : 0<L := div_pos (by positivity) (abs_pos.mpr hg)
  obtain ⟨C,hC,hstep⟩ := shifted_square_step u z
  refine ⟨2*π+C*L^2,by positivity,?_⟩
  intro A
  let p := 2*π/(E b-E a)
  have hp : 0<p := div_pos (by positivity) (sub_pos.mpr hab)
  obtain ⟨l,hl⟩ := exists_nat_gt (max A 0/p)
  have hτ : max A 0 < (l:ℝ)*p := (div_lt_iff₀ hp).mp hl
  let τ := (l:ℝ)*p
  have hτ0 : 0<τ := (le_max_right A 0).trans_lt hτ
  have hturn : τ*(E b-E a)/(2*π)=((l:ℤ):ℝ) := by dsimp only [τ,p]; push_cast; field_simp [(sub_pos.mpr hab).ne']
  refine ⟨τ,hτ0,?_⟩
  intro m hm
  have hm' : (0:ℝ)<m := Nat.cast_pos.mpr hm
  obtain ⟨q,hq,hQ,β,hβ,hwind⟩ := pencil_clock E F a b c
    (fun h => hab.ne (congrArg E h)) (fun h => hca (congrArg E h)) (fun h => hcb (congrArg E h))
    (l:ℤ) hturn hpin (sub_ne_zero.mp hg) hm
  let t := (q:ℝ)*τ
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hD : 3 ≤ D := (by decide : 3≤2^2).trans (Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega))
  have hpow : m*(m^2)^(Fintype.card (Fin (n+2) → Bool)-3)=m^(2*D-5) := by
    rw [show Fintype.card (Fin (n+2) → Bool)=D by simp [D],←pow_mul,←pow_succ']
    congr 1
    omega
  rw [hpow] at hQ
  have hbound : (q:ℝ) ≤ (m:ℝ)^(2*D-5) := by exact_mod_cast hQ
  refine ⟨t,(le_max_left A 0).trans_lt (hτ.trans_le (le_mul_of_one_le_left hτ0.le hq')),?_,?_⟩
  · rw [mul_comm τ]
    exact mul_le_mul_of_nonneg_right hbound hτ0.le
  · have hmetric := quadratic_close H.val H.2.isHermitian z a (by positivity : 0≤1/(m:ℝ)^2) hwind
    have hcir := compose_error hmetric (hstep β)
    obtain ⟨v,hv,G,hG,he⟩ := hcir
    refine ⟨v,hv,G,hG,he.trans ?_⟩
    have hs : β^2 ≤ (L/(m:ℝ))^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg β) (div_pos hL hm').le).mpr hβ
    calc
      _ ≤ 2*π*(1/(m:ℝ)^2)+C*(L/(m:ℝ))^2 := add_le_add_left (mul_le_mul_of_nonneg_left hs hC.le) _
      _ = _ := by ring

#print axioms path_quadratic_deadline
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
