import GaloisForLFunctions.FamilyContinuationTheory.ChordBoundsForMellinReadingsOnTheSecondLine
import GaloisForLFunctions.FamilyContinuationTheory.TheCubicProbeIsACoupledTowerReachingThreeFifths
import GaloisForLFunctions.RHTower.GaussianWindowMomentRescaling

/-!
# Reading the actual cubic Hecke probe on a sparse mesh

Linear interpolation between n^(3/2) and (n+1)^(3/2) costs O(Z^(2/3)).
Consequently every improvement above the two-thirds boundary can be tested
on this mesh. The interval error comes from the finite second moment of
the Gaussian on the inversion line.
-/

noncomputable section
open Complex Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein EisensteinNorm
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The physical receiver in the zero-centered Gaussian cubic probe. -/
def cubicRaySignal (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) :=
  signal (fun s : ℂ => Complex.exp (s^2)*probeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s) 2

private theorem cubic_chords (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {a h q : ℝ}, 0 < a → 0 ≤ h → 0 ≤ q → q ≤ 1 →
      ‖cubicRaySignal 𝔪 η S (a+q*h) - (1-q:ℝ) • cubicRaySignal 𝔪 η S a -
        q • cubicRaySignal 𝔪 η S (a+h)‖ ≤ B*q*(1-q)*h^2 := by
  let G := fun s : ℂ => Complex.exp (s^2)*continuedProbeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s
  have eq : cubicRaySignal 𝔪 η S = signal G 2 := by
    simpa only [cubicRaySignal,G,Complex.ofReal_zero,sub_zero] using
      signal_probeCorrection_eq_continuedProbeCorrection 𝔪 η S hS 0
  rw [eq]
  have gcont : Continuous fun y => G (linePoint y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let s := linePoint y
    have hs : 1 < s.re := by change 1 < (linePoint y).re; rw [linePoint_re]; norm_num
    have hhalf : s ∈ {z : ℂ | 1/2 < z.re} := (by norm_num : (1:ℝ)/2 < 1).trans hs
    have d := (differentiableOn_continuedProbeCorrection 𝔪 η S).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hhalf)
    have g : DifferentiableAt ℂ G s := ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z^2)) s).mul d).div
      (differentiableAt_heckeLFunction 𝔪 η (ne_one_of_one_lt_re hs))
      (heckeLFunction_ne_zero_of_one_lt_re 𝔪 η hs)
    exact g.continuousAt.comp continuous_linePoint.continuousAt
  apply mellin_signal_chord_bound gcont
  let L := Real.exp (-(3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K),
    ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖))
  have lp : 0 < L := Real.exp_pos _
  obtain ⟨M,hM⟩ := exists_norm_continuedProbeCorrection_le 𝔪 η S
  let C := Real.exp 4*|M|/L
  have c0 : 0 ≤ C := div_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) lp.le
  have gauss (y : ℝ) : ‖G (linePoint y)‖ ≤ C*Real.exp (-y^2) := by
    let s := linePoint y
    have re : s.re=2 := linePoint_re y
    have im : s.im= -y := linePoint_im y
    have lower : L ≤ ‖heckeLFunction 𝔪 η s‖ := by
      rw [heckeLFunction_eq_heckeL 𝔪 η (by rw [re]; norm_num)]
      exact exp_neg_le_norm_heckeL 𝔪 η re.ge
    have xe : (s^2).re=4+(-y^2) := by rw [sq,mul_re,re,im]; ring
    change ‖Complex.exp (s^2)*continuedProbeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s‖ ≤ _
    rw [norm_div,norm_mul,norm_exp,xe,Real.exp_add]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ((hM s re.ge).trans (le_abs_self _))
      (by positivity)) (norm_nonneg _)).trans
    apply (div_le_div_of_nonneg_left (by positivity) lp lower).trans_eq
    dsimp only [C]; ring
  have gauss₀ : Integrable (fun y : ℝ => Real.exp (-y^2)) := by
    simpa using _root_.RHTower.integrable_pow_mul_exp_neg_sq 0
  have gi := ((gauss₀.const_mul 4).add (_root_.RHTower.integrable_pow_mul_exp_neg_sq 2)).const_mul C
  apply gi.mono' (by fun_prop)
  apply Eventually.of_forall
  intro y
  let s := linePoint y
  have h₁ : ‖s‖^2=4+y^2 := by rw [Complex.sq_norm,Complex.normSq_apply,linePoint_re,linePoint_im]; ring
  have h₂ : ‖s-1‖^2=1+y^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,sub_re,sub_im,one_re,one_im,linePoint_re,linePoint_im]; ring
  have freq : 1+‖s‖*‖s-1‖ ≤ 4+y^2 := by nlinarith only [h₁,h₂,sq_nonneg (‖s‖-‖s-1‖)]
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul freq (gauss y) (norm_nonneg _) (by positivity)).trans_eq (by
    change (4+y^2)*(C*Real.exp (-y^2))=C*(4*Real.exp (-y^2)+y^2*Real.exp (-y^2)); ring)

private abbrev mesh (n : ℕ) := (n:ℝ)^(3/2:ℝ)

private theorem mesh_gap (n : ℕ) :
    0 ≤ mesh (n+1)-mesh n ∧ (mesh (n+1)-mesh n)^2 ≤ 4*((n:ℝ)+1) := by
  let b := (n:ℝ)+1
  have order : mesh n ≤ mesh (n+1) := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (Nat.le_succ _)) (by norm_num)
  have der (x : ℝ) (_ : x ∈ Icc (n:ℝ) b) :
      HasDerivWithinAt (fun t : ℝ => t^(3/2:ℝ)) ((3/2)*x^(1/2:ℝ)) (Icc n b) x := by
    simpa only [show (3/2:ℝ)-1=1/2 by norm_num] using
      (Real.hasDerivAt_rpow_const (x:=x) (p:=3/2) (Or.inr (by norm_num))).hasDerivWithinAt
  have b0 : 0 ≤ b := by dsimp [b]; positivity
  have hder (x : ℝ) (hx : x ∈ Icc (n:ℝ) b) : ‖(3/2:ℝ)*x^(1/2:ℝ)‖ ≤ 2*Real.sqrt b := by
    have x0 := (Nat.cast_nonneg (α:=ℝ) n).trans hx.1
    rw [←Real.sqrt_eq_rpow,Real.norm_of_nonneg (by positivity)]
    linarith only [Real.sqrt_le_sqrt hx.2,Real.sqrt_nonneg b]
  have nb : (n:ℝ) ≤ b := le_add_of_nonneg_right zero_le_one
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le der hder (convex_Icc ..)
    (left_mem_Icc.mpr nb) (right_mem_Icc.mpr nb)
  have norm : ‖b-(n:ℝ)‖=1 := by dsimp [b]; rw [add_sub_cancel_left]; norm_num
  rw [norm,mul_one,Real.norm_eq_abs] at h
  have gap : mesh (n+1)-mesh n ≤ 2*Real.sqrt b := by
    simpa only [mesh,Nat.cast_succ] using (le_abs_self _).trans h
  refine ⟨sub_nonneg.mpr order,((sq_le_sq₀ (sub_nonneg.mpr order) (by positivity)).mpr gap).trans_eq ?_⟩
  rw [mul_pow,Real.sq_sqrt b0]; ring

/-- On the cubic probe, a power estimate of exponent b≥2/3 on integer
three-halves powers is equivalent to the same estimate on the entire
positive real tail. Endpoints at the critical sampling exponent are included. -/
theorem cubic_probe_three_halves_sampling (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S)
    {b : ℝ} (hb : 2/3 ≤ b) :
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ‖cubicRaySignal 𝔪 η S ((n:ℝ)^(3/2:ℝ))‖ ≤ C*((n:ℝ)^(3/2:ℝ))^b) ↔
      ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ‖cubicRaySignal 𝔪 η S x‖ ≤ C*x^b := by
  let f := cubicRaySignal 𝔪 η S
  have bp : 0 ≤ b := (by norm_num : (0:ℝ) ≤ 2/3).trans hb
  have mt : Tendsto mesh atTop atTop := (tendsto_rpow_atTop (by norm_num : 0<(3/2:ℝ))).comp tendsto_natCast_atTop_atTop
  refine ⟨?_,fun ⟨C,h⟩ => ⟨C,mt h⟩⟩
  rintro ⟨C,hC⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  obtain ⟨B,B0,chord⟩ := cubic_chords 𝔪 η S hS
  let D := |C|*(4:ℝ)^b
  have D0 : 0 ≤ D := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨8*B+D,?_⟩
  filter_upwards [(tendsto_rpow_atTop (by norm_num : 0<(2/3:ℝ))).eventually_ge_atTop (max (N:ℝ) 1),
    eventually_ge_atTop (1:ℝ)] with x high x1
  let n := ⌊x^(2/3:ℝ)⌋₊
  have nN : N ≤ n := Nat.le_floor ((le_max_left ..).trans high)
  have np : 1 ≤ n := Nat.le_floor (by exact_mod_cast (le_max_right ..).trans high : (1:ℝ) ≤ x^(2/3:ℝ))
  have n1 := (Nat.one_le_cast (α:=ℝ)).mpr np
  have x0 := zero_lt_one.trans_le x1
  have inv : (x^(2/3:ℝ))^(3/2:ℝ)=x := by rw [←Real.rpow_mul x0.le]; norm_num
  have low : mesh n ≤ x := (Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.floor_le (Real.rpow_nonneg x0.le _))
    (by norm_num : 0 ≤ (3/2:ℝ))).trans_eq inv
  have high' : x < mesh (n+1) := by
    rw [←inv]
    apply Real.rpow_lt_rpow (Real.rpow_nonneg x0.le _) _ (by norm_num)
    simpa only [Nat.cast_succ] using Nat.lt_floor_add_one (x^(2/3:ℝ))
  let gap := mesh (n+1)-mesh n
  have gp : 0 < gap := sub_pos.mpr (low.trans_lt high')
  let q := (x-mesh n)/gap
  have q0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr low) gp.le
  have q1 : q ≤ 1 := (div_le_one gp).mpr (sub_le_sub_right high'.le _)
  have recover : mesh n+q*gap=x := by dsimp only [q]; rw [div_mul_cancel₀ _ gp.ne']; ring
  have right : mesh n+gap=mesh (n+1) := by dsimp only [gap]; ring
  have base : 0 < mesh n := Real.rpow_pos_of_pos (zero_lt_one.trans_le n1) _
  have cap : mesh (n+1) ≤ 4*x := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg (n+1)) (b := 2*(n:ℝ))
      (by rw [Nat.cast_succ]; linarith only [n1]) (by norm_num : (0:ℝ) ≤ 3/2)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n)] at h
    have h2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (3/2:ℝ) ≤ 2)).trans_eq (Real.rpow_two _)
    exact h.trans (mul_le_mul (by norm_num at h2 ⊢; exact h2) low base.le (by norm_num))
  have endpt (m : ℕ) (hm : N ≤ m) (hcap : mesh m ≤ 4*x) : ‖f (mesh m)‖ ≤ D*x^b := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) _) hcap bp
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) x0.le] at hh
    exact (hN m hm).trans ((mul_le_mul (le_abs_self C) hh
      (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) _) (abs_nonneg _)).trans_eq (mul_assoc ..).symm)
  have leftprice := endpt n nN (low.trans (by linarith only [x0]))
  have rightprice := endpt (n+1) (nN.trans (Nat.le_succ _)) cap
  have er := chord base gp.le q0 q1
  rw [recover,right] at er
  have powers := (Nat.floor_le (Real.rpow_nonneg x0.le (2/3:ℝ))).trans (Real.rpow_le_rpow_of_exponent_le x1 hb)
  have gsmall : gap^2 ≤ 8*x^b := (mesh_gap n).2.trans (by linarith only [powers,n1])
  have ru := sub_nonneg.mpr q1
  have ecost : B*q*(1-q)*gap^2 ≤ 8*B*x^b := by
    have p := mul_le_of_le_one_right (mul_nonneg B0 q0) (sub_le_self 1 q0)
    exact ((mul_le_mul_of_nonneg_right (p.trans (mul_le_of_le_one_right B0 q1)) (sq_nonneg gap)).trans
      (mul_le_mul_of_nonneg_left gsmall B0)).trans_eq (by ring)
  have tri := norm_add_le (f x-(1-q:ℝ) • f (mesh n)-q • f (mesh (n+1)))
    ((1-q:ℝ) • f (mesh n)+q • f (mesh (n+1)))
  rw [show _-_ - _ + (_+_) = f x by abel] at tri
  have endpoints := norm_add_le ((1-q:ℝ) • f (mesh n)) (q • f (mesh (n+1)))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ru,abs_of_nonneg q0] at endpoints
  have paid := endpoints.trans (add_le_add (mul_le_mul_of_nonneg_left leftprice ru) (mul_le_mul_of_nonneg_left rightprice q0))
  exact tri.trans ((add_le_add (er.trans ecost) paid).trans_eq (by ring))

/-- Either the entire Hecke family is zero free above two thirds, or one
candidate frontier forces character signals arbitrarily far above each
smaller power, already at the sparse three-halves observations. -/
theorem hecke_half_plane_or_sparse_cubic_excursions (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) :
    (HeckeHalfPlane K (2/3) ∧ _root_.RHTower.zetaZeroAbscissa ≤ 2/3) ∨
    ∃ β : ℝ, 2/3 < β ∧ β ≤ 1 ∧ HeckeHalfPlane K β ∧ ∀ b : ℝ, 2/3 ≤ b → b < β →
      ∃ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫, ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
        C*((n:ℝ)^(3/2:ℝ))^b < ‖cubicRaySignal η.1 η.2 S ((n:ℝ)^(3/2:ℝ))‖ := by
  classical
  by_cases h : ∀ β : ℝ, 2/3 < β → β ≤ 1 → HeckeHalfPlane K β →
    ∃ b : ℝ, 2/3 ≤ b ∧ b < β ∧ ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ‖cubicRaySignal η.1 η.2 S (mesh n)‖ ≤ C*(mesh n)^b
  · have hp : HeckeHalfPlane K (2/3) := by
      apply heckeHalfPlane_of_probe_estimates_down_to_two_thirds le_rfl (by norm_num) S hS 0
      intro β hβ β1 free
      obtain ⟨b,hb,bs,obs⟩ := h β hβ β1 (fun 𝔪 η => free ⟨𝔪,η⟩)
      refine ⟨b,b,bs,bs,fun η => ?_⟩
      obtain ⟨C,hC⟩ := (cubic_probe_three_halves_sampling η.1 η.2 S hS hb).mp (obs η)
      obtain ⟨Z,hZ⟩ := eventually_atTop.mp hC
      refine ⟨cubicRaySignal η.1 η.2 S,|C|,max 1 Z,le_max_left ..,fun x hx => ?_,fun x hx => ?_⟩
      · exact (hZ x ((le_max_right ..).trans hx)).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg
            (zero_le_one.trans ((le_max_left ..).trans hx)) _))
      · simp only [cubicRaySignal,Complex.ofReal_zero,sub_zero,sub_self,norm_zero]
        exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (zero_le_one.trans ((le_max_left ..).trans hx)) _)
    exact Or.inl ⟨hp,zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic hp⟩
  · push Not at h
    obtain ⟨β,hβ,β1,free,bad⟩ := h
    refine Or.inr ⟨β,hβ,β1,free,fun b hb bs => ?_⟩
    obtain ⟨η,hη⟩ := bad b hb bs
    exact ⟨η,fun C => by simpa only [not_eventually,not_le] using hη C⟩

#print axioms hecke_half_plane_or_sparse_cubic_excursions
#print axioms cubic_probe_three_halves_sampling
end GaloisForLFunctions.FamilyContinuationTheory
