import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Lagrange

/-!
# Residues from a finite set of nearby point readings

The barycentric sum of the values of a holomorphic function equals its
Cauchy integral divided by the nodal polynomial. For a simple pole,
multiplying the same sum by the nodal polynomial at the pole recovers
its residue with a geometric error in the number of sites. The bound
uses only the observation radius and a bound for the regular part.
-/

noncomputable section
open Complex Filter Finset Metric Polynomial Set Topology
open scoped Real
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Signed reading at the center from samples at the distinct sites in t. -/
def barycentricResidue (t : Finset ℂ) (p : ℂ) (f : ℂ → ℂ) : ℂ :=
  -(∏ x ∈ t, (p-x))*(∑ x ∈ t, Lagrange.nodalWeight t id x*f x)

private theorem kernel_identity {t : Finset ℂ} (ht : t.Nonempty) {z : ℂ} (hz : z∉t) :
    ∑ x ∈ t, Lagrange.nodalWeight t id x*(z-x)⁻¹ = (∏ x ∈ t, (z-x))⁻¹ := by
  classical
  have hne (x : ℂ) (hx : x∈t) : z≠id x := fun he => hz (he ▸ hx)
  have h := Lagrange.eval_interpolate_not_at_node (1:ℂ → ℂ) hne
  rw [Lagrange.interpolate_one (Function.injective_id.injOn) ht,Polynomial.eval_one,Lagrange.eval_nodal] at h
  simp only [id_eq,Pi.one_apply,mul_one] at h
  have hn : (∏ x ∈ t, (z-x))≠0 :=
    Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero.mpr (hne x hx)
  calc _ = (∏ x ∈ t, (z-x))⁻¹*((∏ x ∈ t, (z-x))*∑ x ∈ t, Lagrange.nodalWeight t id x*(z-x)⁻¹) :=
             (inv_mul_cancel_left₀ hn _).symm
       _ = _ := by rw [←h,mul_one]

/-- Exact contour expression for the weighted sum, at arbitrary distinct
complex sites strictly inside the circle. -/
theorem barycentric_cauchy_sum {g : ℂ → ℂ} {p : ℂ} {R : ℝ} (hR : 0<R)
    (hg : DifferentiableOn ℂ g (closedBall p R)) {t : Finset ℂ} (ht : t.Nonempty)
    (hsites : ∀ x ∈ t, x∈ball p R) :
    (∮ z in C(p,R), (∏ x ∈ t, (z-x))⁻¹*g z) =
      (2*(Real.pi:ℂ)*I)*(∑ x ∈ t, Lagrange.nodalWeight t id x*g x) := by
  classical
  let w (x : ℂ) := Lagrange.nodalWeight t id x
  let K (x z : ℂ) := w x • ((z-x)⁻¹ • g z)
  have hdis {x z : ℂ} (hx : x∈t) (hz : z∈sphere p R) : z≠x := by
    intro he; subst z
    exact (mem_ball.mp (hsites x hx)).ne (mem_sphere.mp hz)
  have hi (x : ℂ) (hx : x∈t) : CircleIntegrable (K x) p R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact (continuousOn_const (c := w x)).smul (((continuous_id.sub continuous_const).continuousOn.inv₀
      (fun z hz => sub_ne_zero.mpr (hdis hx hz))).smul
      (hg.continuousOn.mono sphere_subset_closedBall))
  calc _ = ∮ z in C(p,R), ∑ x ∈ t, K x z := by
             apply circleIntegral.integral_congr hR.le
             intro z hz
             have hn : z∉t := fun h => hdis h hz rfl
             dsimp only
             rw [←kernel_identity ht hn,Finset.sum_mul]
             exact Finset.sum_congr rfl fun x _ => by simp only [K,w,smul_eq_mul,mul_assoc]
       _ = ∑ x ∈ t, ∮ z in C(p,R), K x z := circleIntegral.integral_fun_sum hi
       _ = _ := by
             rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro x hx
             dsimp only [K]
             rw [circleIntegral.integral_smul,hg.circleIntegral_sub_inv_smul (hsites x hx)]
             simp only [w,smul_eq_mul]; ring

/-- For N sites within d of p, the residue error is at most
R M (d/(R−d))ᴺ. Here M bounds the regular part on the circle. -/
theorem barycentric_pole_error {g : ℂ → ℂ} (m p : ℂ) {R d M : ℝ}
    (hd : 0≤d) (hdr : d<R) (hM : 0≤M) (hg : DifferentiableOn ℂ g (closedBall p R))
    (hbd : ∀ z ∈ sphere p R, ‖g z‖≤M) {t : Finset ℂ} (ht : t.Nonempty) (hp : p∉t)
    (hs : ∀ x ∈ t, dist x p≤d) :
    ‖barycentricResidue t p (fun z => m/(z-p)+g z)-m‖ ≤ R*M*(d/(R-d))^t.card := by
  classical
  have hR := hd.trans_lt hdr
  have hgap := sub_pos.mpr hdr
  let P := ∏ x ∈ t, (p-x)
  let S := ∑ x ∈ t, Lagrange.nodalWeight t id x*g x
  have hP : P≠0 := Finset.prod_ne_zero_iff.mpr fun x hx => sub_ne_zero.mpr fun he => hp (he ▸ hx)
  have hpole : ∑ x ∈ t, Lagrange.nodalWeight t id x*(m/(x-p)) = -m*P⁻¹ := by
    change _= -m*(∏ x ∈ t, (p-x))⁻¹
    rw [←kernel_identity ht hp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [show x-p= -(p-x) by abel,div_neg,div_eq_mul_inv]
    ring
  have err : barycentricResidue t p (fun z => m/(z-p)+g z)-m= -P*S := by
    unfold barycentricResidue
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,hpole]
    change -P*(-m*P⁻¹+S)-m=_
    field_simp [hP] <;> ring
  have hpn : ‖P‖≤d^t.card := by
    dsimp only [P]
    rw [norm_prod]
    calc _ ≤ ∏ _x ∈ t, d := Finset.prod_le_prod (fun x _ => norm_nonneg _) (fun x hx => by
             simpa only [←dist_eq_norm,dist_comm p x] using hs x hx)
         _ = _ := by simp
  have hS : ‖S‖≤R*(M/(R-d)^t.card) := by
    have h := circleIntegral.norm_integral_le_of_norm_le_const (f:=fun z => (∏ x ∈ t, (z-x))⁻¹*g z)
      (c:=p) hR.le (C:=M/(R-d)^t.card) (by
        intro z hz
        have low (x : ℂ) (hx : x∈t) : R-d≤‖z-x‖ := by
          have htri := dist_triangle z x p
          rw [mem_sphere.mp hz,dist_eq_norm z x] at htri
          linarith only [htri,hs x hx]
        have hprod : (R-d)^t.card≤∏ x ∈ t, ‖z-x‖ := by
          simpa only [Finset.prod_const] using Finset.prod_le_prod (s:=t)
            (f:=fun _ => R-d) (g:=fun x => ‖z-x‖) (fun _ _ => hgap.le) low
        rw [norm_mul,norm_inv,norm_prod,←div_eq_inv_mul]
        exact div_le_div₀ hM (hbd z hz) (pow_pos hgap _) hprod)
    rw [barycentric_cauchy_sum hR hg ht (fun x hx => (hs x hx).trans_lt hdr),norm_mul] at h
    have hnorm : ‖2*(Real.pi:ℂ)*I‖=2*Real.pi := by
      rw [norm_mul,norm_mul,Complex.norm_two,Complex.norm_I,mul_one,
        Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    rw [hnorm] at h
    have h2 : 2*Real.pi*‖S‖ ≤ 2*Real.pi*(R*(M/(R-d)^t.card)) := by
      rw [← mul_assoc]; exact h
    exact (mul_le_mul_iff_right₀ Real.two_pi_pos).mp h2
  rw [err,norm_mul,norm_neg]
  exact (mul_le_mul hpn hS (norm_nonneg _) (pow_nonneg hd _)).trans_eq (by
    rw [div_pow]; ring)

/-- A calibration polynomial of degree below N−1 makes exactly zero
contribution at N sites. Its coefficients may depend on the sites. -/
theorem barycentric_polynomial_drift (t : Finset ℂ) (p : ℂ) (f : ℂ → ℂ) (P : ℂ[X])
    (hP : P.natDegree+1<t.card) :
    barycentricResidue t p (fun z => f z+P.eval z)=barycentricResidue t p f := by
  classical
  have hd : P.degree < (t.card:WithBot ℕ) := P.degree_le_natDegree.trans_lt
    (by exact_mod_cast (show P.natDegree<t.card by omega))
  have hc := Lagrange.coeff_eq_sum (v:=id) (s:=t) Function.injective_id.injOn hd
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<t.card-1)] at hc
  have hz : (∑ x ∈ t, Lagrange.nodalWeight t id x*P.eval x)=0 := by
    calc _ = ∑ i ∈ t, P.eval i / ∏ j ∈ t.erase i, (i-j) := by
               apply Finset.sum_congr rfl
               intro i _
               rw [Lagrange.nodalWeight,Finset.prod_inv_distrib,div_eq_mul_inv,mul_comm]
               rfl
         _ = _ := hc.symm
  unfold barycentricResidue
  simp only [mul_add,Finset.sum_add_distrib,hz,add_zero]

#print axioms barycentric_polynomial_drift
#print axioms barycentric_cauchy_sum
#print axioms barycentric_pole_error
end GaloisForLFunctions.ExceptionalLayerTheory
