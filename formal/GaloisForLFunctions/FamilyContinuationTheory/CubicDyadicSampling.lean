import GaloisForLFunctions.FamilyContinuationTheory.TheCubicProbeIsACoupledTowerReachingThreeFifths
import GaloisForLFunctions.RHTower.CarrierDepthThreeOffLineZeros

/-!
# The cubic probe from a dilation difference and one geometric sequence

At a candidate boundary, a dyadic first difference cannot see a
log-periodic leading term. Triadic samples meet every phase of that
period. A power gain for the difference and qualitative vanishing
on the triadic sequence give the same power gain for the full probe.
This uses the phase separation mechanism for multiplicative orbits in
El Kaouni's trace argument.
-/

noncomputable section
open Filter Topology Complex Set Metric NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open _root_.RHTower EisensteinNorm

private theorem iterate_difference {U : ℝ → ℂ} {d C T : ℝ} (hd : 0<d) (hC : 0≤C)
    (hstep : ∀ x, T≤x → ‖U (x+1)-U x‖ ≤ C*Real.exp (-d*x)) {y : ℝ} (hy : T≤y) (k : ℕ) :
    ‖U (y+k)-U y‖ ≤ C*Real.exp (-d*y)/(1-Real.exp (-d)) := by
  let q := Real.exp (-d)
  have hq : 0<q := Real.exp_pos _
  have hq₁ : q<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hd)
  let A := C*Real.exp (-d*y)/(1-q)
  have hA : 0≤A := div_nonneg (mul_nonneg hC (Real.exp_pos _).le) (sub_pos.mpr hq₁).le
  have hinc (j : ℕ) : ‖U (y+j+1)-U (y+j)‖ ≤ C*Real.exp (-d*y)*q^j := by
    have he : Real.exp (-d*(y+j))=Real.exp (-d*y)*q^j := by
      rw [show -d*(y+j)= -d*y+(j:ℝ)*(-d) by ring,Real.exp_add,Real.exp_nat_mul]
    simpa only [he,mul_assoc] using hstep (y+j) (hy.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hgeom (j : ℕ) : ‖U (y+j)-U y‖ ≤ A*(1-q^j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ,←add_assoc]
      calc ‖U (y+j+1)-U y‖ ≤ ‖U (y+j+1)-U (y+j)‖+‖U (y+j)-U y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
           _ ≤ _ := add_le_add (hinc j) ih
           _ = _ := by
             dsimp only [A]
             rw [pow_succ]
             field_simp [(sub_pos.mpr hq₁).ne']
             ring
  exact (hgeom k).trans (mul_le_of_le_one_right hA (by linarith only [pow_nonneg hq.le k]))

/-- A decaying unit-step difference determines the full rate from
qualitative vanishing along a single irrational arithmetic progression.
The constant depends only on the size of the difference and its rate. -/
theorem geometric_sampling_bound {U : ℝ → ℂ} (hU : Continuous U) {α d C T : ℝ}
    (hα : Irrational α) (hα₀ : 0<α) (hd : 0<d) (hC : 0≤C)
    (hstep : ∀ x, T≤x → ‖U (x+1)-U x‖≤C*Real.exp (-d*x))
    (hsample : Tendsto (fun n : ℕ => U (n*α)) atTop (𝓝 0)) {x : ℝ} (hx : T<x) :
    ‖U x‖ ≤ C*Real.exp (-d*x)/(1-Real.exp (-d)) := by
  let B := fun y : ℝ => C*Real.exp (-d*y)/(1-Real.exp (-d))
  have hB : Continuous B := by dsimp only [B]; fun_prop
  change ‖U x‖≤B x
  by_contra! hh
  let ε := (‖U x‖-B x)/2
  have he : 0<ε := by dsimp [ε]; linarith only [hh]
  have hg : ∀ᶠ y in 𝓝 x, T<y ∧ B y+ε<‖U y‖ :=
    (eventually_gt_nhds hx).and ((isOpen_lt (hB.add continuous_const) hU.norm).mem_nhds
      (by change B x+ε<‖U x‖; dsimp [ε]; linarith only [hh]))
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp hg
  have hs := hsample.norm.eventually_lt_const (by simpa using he : ‖(0:ℂ)‖<ε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hs
  let M := max N ⌈(x+r)/α⌉₊
  obtain ⟨k,hk,j,hj⟩ := CarrierDepthThree.exists_nat_mul_near hα x hr M
  have hbase : x+r ≤ (k:ℝ)*α := by
    apply (div_le_iff₀ hα₀).mp
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hk))
  have hj₀ : 0≤j := by
    have h := (abs_lt.mp hj).2
    exact_mod_cast (show (0:ℝ) ≤ j by linarith only [hbase,h])
  let y := (k:ℝ)*α-(j:ℝ)
  have hdist : dist y x < r := by
    rw [Real.dist_eq]
    simpa only [y,sub_right_comm] using hj
  obtain ⟨hy,hbad⟩ := hrb hdist
  have htel := iterate_difference hd hC hstep hy.le j.toNat
  have hid : y+(j.toNat:ℝ)=k*α := by
    have hcast : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj₀
    dsimp only [y]; rw [hcast]; ring
  rw [hid] at htel
  have hsmall := hN k ((le_max_left _ _).trans hk)
  have htri := norm_sub_norm_le (U y) (U (k*α))
  rw [norm_sub_rev] at htri
  linarith only [hbad,hsmall,htri,htel]

/-- The irrationality requirement is sharp. A rational phase with
denominator b misses the continuous unit-periodic sine of frequency b,
even if all samples are known exactly. -/
theorem periodic_sampling_iff_irrational {α : ℝ} (hα₀ : 0<α) :
    (∀ U : ℝ → ℂ, Continuous U → Function.Periodic U 1 →
      Tendsto (fun n : ℕ => U (n*α)) atTop (𝓝 0) → ∀ x, U x=0) ↔ Irrational α := by
  constructor
  · intro h
    by_contra hr
    obtain ⟨q,hq⟩ := exists_rat_of_not_irrational hr
    let b : ℝ := q.den
    let U := fun x : ℝ => (Real.sin (b*(2*Real.pi)*x):ℂ)
    have hb : b ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hratio : b*α=(q.num:ℝ) := by
      rw [hq,Rat.cast_def]; change (q.den:ℝ)*_=_; field_simp
    have hper : Function.Periodic U 1 := fun x => by
      dsimp only [U]
      rw [show b*(2*Real.pi)*(x+1)=b*(2*Real.pi)*x+(q.den:ℝ)*(2*Real.pi) by dsimp only [b]; ring,
        Real.sin_add_nat_mul_two_pi]
    have hval (n : ℕ) : U (n*α)=0 := by
      have he : b*(2*Real.pi)*((n:ℝ)*α)=((2*(n:ℤ)*q.num:ℤ):ℝ)*Real.pi := by
        push_cast; rw [←hratio]; ring
      simp only [U,he,Real.sin_int_mul_pi,Complex.ofReal_zero]
    have he := h U (by dsimp only [U]; fun_prop) hper (by simpa only [hval] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))) (1/(4*b))
    have hphase : b*(2*Real.pi)*(1/(4*b))=Real.pi/2 := by field_simp; ring
    simp only [U,hphase,Real.sin_pi_div_two,Complex.ofReal_one] at he
    exact one_ne_zero he
  · intro hα U hU hp hs x
    have hi := geometric_sampling_bound (U := U) (d := 1) (C := 0) (T := x-1) hU hα hα₀
      zero_lt_one le_rfl (fun y _ => by rw [hp y,sub_self,norm_zero,zero_mul]) hs (by linarith : x-1<x)
    simpa only [zero_mul,zero_div,norm_le_zero_iff] using hi


/-- Boundary-normalized reading in logarithmic coordinates to base two. -/
def dyadicReading (F : ℝ → ℂ) (β x : ℝ) : ℂ :=
  (Real.exp (-β*(Real.log 2*x)):ℂ)*F (Real.exp (Real.log 2*x))

private theorem norm_reading (F : ℝ → ℂ) (β x : ℝ) :
    ‖dyadicReading F β x‖=Real.exp (-β*(Real.log 2*x))*‖F (Real.exp (Real.log 2*x))‖ := by
  rw [dyadicReading,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

/-- A full O(Z^a) estimate is equivalent to a dyadic increment estimate
at that power together with o(3^(nβ)) on the triadic samples. The two
rates may be arbitrarily close, with a strictly positive gap. -/
theorem power_bound_iff_dyadic_and_triadic {F : ℝ → ℂ} (hf : ContinuousOn F (Ioi 0))
    {a β : ℝ} (hgap : a<β) :
    (∃ C Z₀ : ℝ, 1≤Z₀ ∧ ∀ Z, Z₀≤Z → ‖F Z‖≤C*Z^a) ↔
      (∃ C T : ℝ, 0≤C ∧ ∀ x, T≤x →
        ‖dyadicReading F β (x+1)-dyadicReading F β x‖≤C*Real.exp (-(β-a)*(Real.log 2*x))) ∧
      Tendsto (fun n : ℕ => ((3:ℝ) ^ (-(n:ℝ)*β):ℝ) • F ((3:ℝ)^n)) atTop (𝓝 0) := by
  let U := dyadicReading F β
  let l := Real.log 2
  let α := Real.log 3/l
  let d := (β-a)*l
  have hl : 0<l := Real.log_pos (by norm_num)
  have hα₀ : 0<α := div_pos (Real.log_pos (by norm_num)) hl
  have hd : 0<d := mul_pos (sub_pos.mpr hgap) hl
  have hU : Continuous U := by
    have hg : Continuous (fun x : ℝ => Real.exp (l*x)) := by fun_prop
    exact (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => Real.exp (-β*(l*x)))).mul
      (hf.comp_continuous hg fun x => Real.exp_pos _)
  have heq (x : ℝ) : -(β-a)*(l*x)= -d*x := by dsimp only [d]; ring
  have hpoint (n : ℕ) : U (n*α)=((3:ℝ)^(-(n:ℝ)*β)) • F ((3:ℝ)^n) := by
    have hlog : l*((n:ℝ)*α)=(n:ℝ)*Real.log 3 := by dsimp only [α]; field_simp [hl.ne']
    change (Real.exp (-β*(l*(n*α))):ℂ)*F (Real.exp (l*(n*α)))=_
    rw [hlog,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<3),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
    rw [show -β*((n:ℝ)*Real.log 3)=Real.log 3*(-(n:ℝ)*β) by ring]
    rfl
  have hex (C x : ℝ) :
      ‖U x‖ ≤ C*Real.exp (-d*x) ↔ ‖F (Real.exp (l*x))‖ ≤ C*(Real.exp (l*x))^a := by
    rw [show ‖U x‖=_ from norm_reading F β x,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    change Real.exp (-β*(l*x))*_≤_ ↔ _
    have hid : Real.exp (-d*x)=Real.exp (-β*(l*x))*Real.exp (l*x*a) := by
      rw [←Real.exp_add]; congr 1; dsimp [d]; ring
    rw [hid,mul_left_comm C,mul_le_mul_iff_right₀ (Real.exp_pos _)]
  constructor
  · rintro ⟨C,Z,hZ,hbound⟩
    let C' := max C 0
    let T := Real.log Z/l
    have hC : 0≤C' := le_max_right _ _
    have hb (x : ℝ) (hx : T≤x) : ‖U x‖≤C'*Real.exp (-d*x) := by
      apply (hex C' x).mpr
      have hZ₀ : 0<Z := zero_lt_one.trans_le hZ
      have harg : Z≤Real.exp (l*x) := by
        rw [← Real.log_le_log_iff hZ₀ (Real.exp_pos _),Real.log_exp,mul_comm]
        exact (div_le_iff₀ hl).mp hx
      exact (hbound _ harg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.exp_pos _).le _))
    constructor
    · refine ⟨2*C',T,by positivity,fun x hx => ?_⟩
      rw [heq]
      have h₁ := hb (x+1) (by linarith)
      have h₂ := hb x hx
      have hle := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hd] : -d*(x+1)≤ -d*x)) hC
      exact (norm_sub_le _ _).trans (by linarith only [h₁.trans hle,h₂])
    · simp_rw [←hpoint]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have htime := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hα₀
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      · exact htime.eventually (eventually_atTop.mpr ⟨T,hb⟩)
      · have hdec := Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hd)).mpr htime)
        simpa only [mul_zero,Function.comp_apply] using hdec.const_mul C'
  · rintro ⟨⟨C,T,hC,hstep⟩,hs⟩
    simp_rw [← hpoint] at hs
    let B := C/(1-Real.exp (-d))
    let Z := Real.exp (l*(max T 0+1))
    refine ⟨B,Z,?_,fun z hz => ?_⟩
    · change 1≤Real.exp _
      exact Real.one_le_exp (mul_nonneg hl.le (by linarith only [le_max_right T 0]))
    · have hz₀ := (Real.exp_pos _).trans_le hz
      let x := Real.log z/l
      have hlog : l*x=Real.log z := by dsimp [x]; field_simp
      have hx : T<x := by
        have h := Real.log_le_log (Real.exp_pos _) hz
        rw [Real.log_exp,←hlog] at h
        linarith only [(mul_le_mul_iff_right₀ hl).mp h,le_max_left T 0]
      have h := geometric_sampling_bound hU CarrierDepthThree.irrational_log_three_div_log_two hα₀ hd hC
        (fun y hy => by simpa only [← heq] using hstep y hy) hs hx
      have hb : ‖U x‖≤B*Real.exp (-d*x) := h.trans_eq (by dsimp only [B]; ring)
      simpa only [hlog,Real.exp_log hz₀] using (hex B x).mp hb

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- Corrected reciprocal cubic signal on the original integration line. -/
def cubicProbeReading (η : Σ 𝔪 : Modulus K, HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) : ℝ → ℂ :=
  signal (fun s : ℂ => Complex.exp (s^2)*probeCorrection η.1 η.2 S s/heckeLFunction η.1 η.2 s) 2

private theorem continuous_probe (η : Σ 𝔪 : Modulus K, HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm≤160 → v∈S) :
    ContinuousOn (cubicProbeReading η S) (Ioi 0) := by
  have he := signal_probeCorrection_eq_continuedProbeCorrection η.1 η.2 S hS 0
  simp only [Complex.ofReal_zero,sub_zero] at he
  unfold cubicProbeReading
  rw [he]
  apply continuousOn_signal_two
  obtain ⟨C,hC⟩ := exists_norm_continuedProbeCorrection_le η.1 η.2 S
  have hopen : IsOpen {s:ℂ | 1/2<s.re} := isOpen_lt continuous_const continuous_re
  simpa only [Complex.ofReal_zero,sub_zero] using
    isSignalKernel_gauss_mul_div_of_bounded (Real.exp_pos _)
      (fun s hs => differentiableAt_heckeLFunction η.1 η.2 (ne_one_of_one_lt_re hs))
      (fun s hs => heckeLFunction_ne_zero_of_one_lt_re η.1 η.2 hs)
      (fun s hs => by
        rw [heckeLFunction_eq_heckeL η.1 η.2 (by linarith : 1<s.re)]
        exact exp_neg_le_norm_heckeL η.1 η.2 hs)
      (fun s hs => (differentiableOn_continuedProbeCorrection η.1 η.2 S).differentiableAt
        (hopen.mem_nhds (by change (1:ℝ)/2<s.re; linarith)))
      hC 0

/-- At each candidate boundary the full power gain for the cubic Hecke
family amounts to a gain for the dyadic increments and qualitative
boundary decay along powers of three. The exponent is common to all
characters; every estimate constant may depend on the character. -/
theorem cubic_family_dyadic_sampling (β : ℝ) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O,v.asIdeal.absNorm≤160 → v∈S) :
    (∃ a : ℝ, a<β ∧ ∀ η, ∃ C Z₀ : ℝ, 1≤Z₀ ∧
      ∀ Z, Z₀≤Z → ‖cubicProbeReading η S Z‖≤C*Z^a) ↔
    ∃ a : ℝ, a<β ∧ ∀ η,
      (∃ C T : ℝ, 0≤C ∧ ∀ x, T≤x →
        ‖dyadicReading (cubicProbeReading η S) β (x+1)-dyadicReading (cubicProbeReading η S) β x‖
          ≤ C*Real.exp (-(β-a)*(Real.log 2*x))) ∧
      Tendsto (fun n : ℕ => ((3:ℝ)^(-(n:ℝ)*β)) • cubicProbeReading η S ((3:ℝ)^n)) atTop (𝓝 0) := by
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  exact forall_congr' fun η => power_bound_iff_dyadic_and_triadic (continuous_probe η S hS) ha

/-- All prime ideals in the prescribed norm cutoff of the cubic probe. -/
def cubicPrimeCutoff : Finset (HeightOneSpectrum O) :=
  (show {v : HeightOneSpectrum O | v.asIdeal.absNorm≤160}.Finite from
    (Ideal.finite_setOf_absNorm_le (S := O) 160).preimage
      (f := fun v : HeightOneSpectrum O => v.asIdeal) (fun _ _ _ _ h => HeightOneSpectrum.ext h)).toFinset

private theorem mem_cubicPrimeCutoff (v : HeightOneSpectrum O) :
    v ∈ cubicPrimeCutoff ↔ v.asIdeal.absNorm≤160 := by simp [cubicPrimeCutoff]

/-- The dyadic/triadic criterion on the actual corrected probe has the
full two-thirds reach, both for the Hecke family and for ordinary zeta. -/
theorem two_thirds_of_dyadic_probe_sampling :
    let S := cubicPrimeCutoff
    (∀ β : ℝ, 2/3<β → β≤1 →
      (∀ (η : Σ 𝔪 : Modulus K, HeckeCharacter 𝔪) (ρ : ℂ),
        β<ρ.re → ρ≠1 → heckeLFunction η.1 η.2 ρ≠0) →
      ∃ a : ℝ, a<β ∧ ∀ η,
        (∃ C T : ℝ, 0≤C ∧ ∀ x, T≤x →
          ‖dyadicReading (cubicProbeReading η S) β (x+1)-dyadicReading (cubicProbeReading η S) β x‖
            ≤ C*Real.exp (-(β-a)*(Real.log 2*x))) ∧
        Tendsto (fun n : ℕ => ((3:ℝ)^(-(n:ℝ)*β)) • cubicProbeReading η S ((3:ℝ)^n)) atTop (𝓝 0)) →
      HeckeHalfPlane K (2/3) ∧ zetaZeroAbscissa≤2/3 := by
  intro S hint
  have hS (v : HeightOneSpectrum O) : v.asIdeal.absNorm≤160 → v∈S := (mem_cubicPrimeCutoff v).mpr
  have step (β : ℝ) (hβ : 2/3<β) (hβ₁ : β≤1)
      (hfamily : ∀ (η : Σ 𝔪 : Modulus K, HeckeCharacter 𝔪) (ρ : ℂ),
        β<ρ.re → ρ≠1 → heckeLFunction η.1 η.2 ρ≠0) := (cubic_family_dyadic_sampling β S hS).mpr
        (hint β hβ hβ₁ hfamily)
  have hHP : HeckeHalfPlane K (2/3) := by
    apply heckeHalfPlane_of_probe_estimates_down_to_two_thirds le_rfl (by norm_num) S hS 0
    intro β hβ hβ₁ hf
    obtain ⟨a,ha,hη⟩ := step β hβ hβ₁ hf
    refine ⟨a,a,ha,ha,fun η => ?_⟩
    obtain ⟨C,Z,hZ,hbound⟩ := hη η
    refine ⟨cubicProbeReading η S,max C 0,Z,hZ,fun z hz => ?_,fun z hz => ?_⟩
    · exact (hbound z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith only [hZ,hz]) _))
    · simp only [cubicProbeReading,Complex.ofReal_zero,sub_zero,sub_self,norm_zero]
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by linarith only [hZ,hz]) _)

  exact ⟨hHP,zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic hHP⟩

end GaloisForLFunctions.FamilyContinuationTheory
