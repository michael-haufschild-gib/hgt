import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.Polydisc
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.LinearPencil

/-! # Uniform bounds for cleared derivative rows, including at collisions -/
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem tangent_bound (p b : MvPolynomial (Option ι) ℂ) (i : ι) (x : Option ι → ℂ)
    {K M : ℝ} (hp : ∀ j, ‖eval x (pderiv j p)‖ ≤ K)
    (hb : ∀ j, ‖eval x (pderiv j b)‖ ≤ M) :
    ‖eval x (tangent p i b)‖ ≤ 2*K*M := by
  rw [tangent,map_sub,map_mul,map_mul]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  exact (add_le_add (mul_le_mul (hp none) (hb (some i)) (norm_nonneg _) ((norm_nonneg _).trans (hp none)))
    (mul_le_mul (hp (some i)) (hb none) (norm_nonneg _) ((norm_nonneg _).trans (hp (some i))))).trans_eq (by ring)

/-- On a smaller polydisc each step of the implicit-derivative recursion
costs at most (2+4L)K², with no division by a root separation. -/
theorem numerator_box_bound (p : MvPolynomial (Option ι) ℂ) {R K : ℝ} (hp : BoxBound p R K)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (L : ℕ) (w : List ι) (hw : w.length ≤ L)
    {r : ℝ} (hmargin : r + w.length + 2 ≤ R) :
    BoxBound (numerator p w) r (R*((2+4*(L:ℝ))*K^2)^w.length) := by
  induction w generalizing r with
  | nil =>
    intro x hx
    simp only [List.length_nil,Nat.cast_zero,add_zero] at hmargin
    simpa [numerator] using (hx none).trans (show r ≤ R by linarith only [hmargin])
  | cons i w ih =>
    have hlen : w.length+1 ≤ L := hw
    have hroom : r+1+(w.length:ℝ)+2 ≤ R := by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hmargin
      linarith
    let M := R*((2+4*(L:ℝ))*K^2)^w.length
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hb : BoxBound (numerator p w) (r+1) M := ih (by omega) hroom
    have hd (j : Option ι) : BoxBound (pderiv j p) (r+1) K :=
      (hp.shrink (by linarith only [hroom,Nat.cast_nonneg (α := ℝ) w.length])).partial j
    intro x hx
    have hx' (j) := (hx j).trans (show r ≤ r+1 by linarith)
    have h₁ := tangent_bound p (numerator p w) i x (fun j => hd j x hx')
      (fun j => hb.partial j x hx)
    have h₂ := tangent_bound p (pderiv none p) i x (fun j => hd j x hx')
      (fun j => (hd none).partial j x hx)
    rw [numerator,map_sub,map_mul,map_nsmul,nsmul_eq_mul,map_mul]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,Complex.norm_natCast,List.length_cons,Nat.cast_mul,Nat.cast_ofNat,
      show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    rw [pow_succ ((2+4*(L:ℝ))*K^2) w.length]
    have hbnd := add_le_add (mul_le_mul (hd none x hx') h₁ (norm_nonneg _) hK)
      (mul_le_mul_of_nonneg_left (mul_le_mul (hb x hx') h₂ (norm_nonneg _) hM)
        (by positivity : (0:ℝ) ≤ 2*w.length))
    apply hbnd.trans
    have hj : (w.length:ℝ) ≤ L := by exact_mod_cast (show w.length ≤ L by omega)
    calc K*(2*K*M) + 2*w.length*(M*(2*K*K)) = M*((2+4*(w.length:ℝ))*K^2) := by ring
         _ ≤ M*((2+4*(L:ℝ))*K^2) := by gcongr
         _ = _ := by dsimp [M]; ring

/-- Every padded row, including the constant row, has the same upper bound
on the original box. -/
theorem jetRow_box_bound (p : MvPolynomial (Option ι) ℂ) {R K r : ℝ} (hp : BoxBound p R K)
    (hR : 1 ≤ R) (hK : 1 ≤ K) (L : ℕ) (hm : r+(L:ℝ)+2 ≤ R)
    (w : Option (List ι)) (hw : ∀ v ∈ w, v.length ≤ L) :
    BoxBound (jetRow p L w) r (R*(2+4*(L:ℝ))^L * K^(2*L)) := by
  have hKr := zero_le_one.trans hK
  have hd : BoxBound (pderiv none p) r K := (hp.shrink (by linarith only [hm,Nat.cast_nonneg (α := ℝ) L])).partial none
  let F := 2+4*(L:ℝ)
  have hF : 1 ≤ F := by dsimp [F]; linarith only [Nat.cast_nonneg (α := ℝ) L]
  intro x hx
  cases w with
  | none =>
    simp only [jetRow,map_pow,norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hd x hx) _).trans
      (le_mul_of_one_le_left (pow_nonneg hKr _) (one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ hF)))
  | some w =>
    have hj := hw w rfl
    have hj' : (w.length:ℝ) ≤ L := by exact_mod_cast hj
    have hb := numerator_box_bound p hp (zero_le_one.trans hR) hKr L w hj (r := r) (by linarith) x hx
    simp only [jetRow,cleared,map_mul,map_pow,norm_mul,norm_pow]
    apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hd x hx) _) hb (norm_nonneg _) (pow_nonneg hKr _)).trans
    have he : 2*(L-w.length)+2*w.length = 2*L := by omega
    calc K^(2*(L-w.length))*(R*(F*K^2)^w.length) =
           R*F^w.length*(K^(2*(L-w.length))*K^(2*w.length)) := by rw [mul_pow,pow_mul]; ring
         _ = R*F^w.length*K^(2*L) := by rw [← pow_add,he]
         _ ≤ _ := by
           exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hF hj)
             (zero_le_one.trans hR)) (pow_nonneg hKr _)

#print axioms jetRow_box_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets
