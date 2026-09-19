import GaloisForLFunctions.RHTower.MobiusDivisorPrimeCorrelationPhysical
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation

/-!
# Prescribed prime insertion over an inherited core

Two shrinking windows of actual primes produce Euler multipliers approximating
a two-phase exponential. Exact integer-period gates make its complete signed
Mellin integral positive. A global product bound permits dominated convergence,
so the sign transfers to an actual finite preparation beyond any given bound.
The exact physical release identity then forces the prescribed prime to lower
the energy coefficient and the actual energies on a common integer-cutoff tail.

The inherited core is arbitrary and remains present. One quadratic budget,
chosen before the lower bound on helper primes, controls every preparation
subset at every cutoff, both before and after the prescribed insertion.
The budget still depends on the inherited core and prescribed prime; uniform
control across changing cores and exhaustive coverage remain unproved.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower
open GaloisForLFunctions.HTGeometry

private def clusterWindow (η x : ℝ) : Finset ℕ :=
  primesInIoc ⌊x⌋₊ ⌊(1+η)*x⌋₊

private lemma cluster_capacity {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    ∀ᶠx : ℝ in atTop,⌈s*Real.sqrt x⌉₊ ≤ (clusterWindow η x).card := by
  have hc := eventually_primeCount_window_ge (by linarith : (1:ℝ) < 1+η)
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have hsmall := hl.eventually (eventually_lt_nhds (show (0:ℝ) < η/(4*(s+1)) by positivity))
  filter_upwards [hc,hsmall,eventually_gt_atTop (1:ℝ)] with x hc hsmall hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog := Real.log_pos hx
  have hroot := Real.sqrt_pos.mpr hx0
  have hroot1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx.le
  have hxx : x ≤ (1+η)*x := by nlinarith only [mul_pos hη hx0]
  rw [← card_primesInIoc (Nat.floor_le_floor hxx)] at hc
  change ((1+η)-1)/2*(x/Real.log x) ≤ ((clusterWindow η x).card:ℝ) at hc
  rw [← Real.sqrt_eq_rpow] at hsmall
  have hlogsmall : 4*(s+1)*Real.log x < η*Real.sqrt x := by
    have hh := (div_lt_div_iff₀ hroot (show 0 < 4*(s+1) by positivity)).mp hsmall
    nlinarith only [hh]
  have hcount : (s+1)*Real.sqrt x ≤ ((clusterWindow η x).card:ℝ) := by
    apply le_trans _ hc
    calc
      (s+1)*Real.sqrt x ≤ (η/2*x)/Real.log x := by
        apply (le_div_iff₀ hlog).mpr
        have hm := mul_le_mul_of_nonneg_right hlogsmall.le hroot.le
        have hm' : 4*((s+1)*Real.sqrt x*Real.log x) ≤ η*x := by
          calc
            _ = 4*(s+1)*Real.log x*Real.sqrt x := by ring
            _ ≤ η*Real.sqrt x*Real.sqrt x := hm
            _ = η*x := by rw [mul_assoc,← pow_two,Real.sq_sqrt hx0.le]
        nlinarith only [hm',mul_nonneg hη.le hx0.le]
      _ = _ := by ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ s*Real.sqrt x by positivity)
  have hh : (⌈s*Real.sqrt x⌉₊:ℝ) ≤ ((clusterWindow η x).card:ℝ) := by
    nlinarith only [hceil,hcount,hroot1]
  exact_mod_cast hh

private lemma cluster_members {η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ clusterWindow η x) : p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*x := by
  obtain ⟨hp, hlo, hhi⟩ := mem_primesInIoc hp
  refine ⟨hp,(Nat.floor_lt hx).mp hlo,?_⟩
  exact (show (p:ℝ) ≤ ⌊(1+η)*x⌋₊ by exact_mod_cast hhi).trans (Nat.floor_le (by positivity))

private lemma paired_cluster_supply {η s r : ℝ}
    (hη : 0 < η) (hs : 0 < s) (hr : 1+η < r) :
    ∀ᶠ x : ℝ in atTop, ∃ A B : Finset ℕ,
      A.card = ⌈s*Real.sqrt x⌉₊ ∧ B.card = ⌈s*Real.sqrt x⌉₊ ∧ Disjoint A B ∧
      (∀ p ∈ A,p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*x) ∧
      (∀ p ∈ B,p.Prime ∧ r*x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*(r*x)) := by
  have hr0 : 0 < r := by linarith
  have hscale : Tendsto (fun x : ℝ => r*x) atTop atTop := tendsto_id.const_mul_atTop hr0
  have hA := cluster_capacity hη hs.le
  have hB := hscale.eventually hA
  filter_upwards [hA,hB,eventually_gt_atTop (0:ℝ)] with x hA hB hx
  have hxr : x ≤ r*x := by nlinarith only [hr,hη,hx]
  have hn : ⌈s*Real.sqrt x⌉₊ ≤ ⌈s*Real.sqrt (r*x)⌉₊ :=
    Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxr) hs.le)
  obtain ⟨A,hAs,hAc⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨B,hBs,hBc⟩ := Finset.exists_subset_card_eq (hn.trans hB)
  have hdataA : ∀ p ∈ A,p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*x :=
    fun p hp => cluster_members hη.le hx.le (hAs hp)
  have hdataB : ∀ p ∈ B,p.Prime ∧ r*x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*(r*x) :=
    fun p hp => cluster_members hη.le (mul_nonneg hr0.le hx.le) (hBs hp)
  refine ⟨A,B,hAc,hBc,?_,hdataA,hdataB⟩
  apply Finset.disjoint_left.mpr
  intro p hpA hpB
  have hhi := (hdataA p hpA).2.2
  have hlo := (hdataB p hpB).2.1
  nlinarith only [hhi,hlo,mul_lt_mul_of_pos_right hr hx]

private lemma cluster_weight_bounds {η s x : ℝ} (hη : 0 ≤ η) (hs : 0 < s) (hx : 1 ≤ x)
    (A : Finset ℕ) (hcard : A.card=⌈s*Real.sqrt x⌉₊)
    (hA : ∀ p ∈ A,x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*x) :
    s/Real.sqrt (1+η) ≤ ∑ p ∈ A,(Real.sqrt p)⁻¹ ∧
      (∑ p ∈ A,(Real.sqrt p)⁻¹) ≤ s+1/Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hroot := Real.sqrt_pos.mpr hx0
  have hη0 : 0 < 1+η := by linarith
  have hlow : (A.card:ℝ)/Real.sqrt ((1+η)*x) ≤ ∑ p ∈ A,(Real.sqrt p)⁻¹ := by
    have h := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (hx0.trans (hA p hp).1))
        (Real.sqrt_le_sqrt (hA p hp).2))
    simpa only [sum_const,nsmul_eq_mul,one_div,div_eq_mul_inv,one_mul] using h
  have hhigh : (∑ p ∈ A,(Real.sqrt p)⁻¹) ≤ (A.card:ℝ)/Real.sqrt x := by
    have h := sum_le_sum (fun p hp => one_div_le_one_div_of_le hroot
      (Real.sqrt_le_sqrt (hA p hp).1.le))
    simpa only [sum_const,nsmul_eq_mul,one_div,div_eq_mul_inv,one_mul] using h
  rw [hcard] at hlow hhigh
  have hc := Nat.le_ceil (s*Real.sqrt x)
  have hcl := Nat.ceil_lt_add_one (show 0 ≤ s*Real.sqrt x by positivity)
  constructor
  · apply le_trans _ hlow
    rw [Real.sqrt_mul hη0.le]
    apply (le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr hη0) hroot)).mpr
    calc
      s/Real.sqrt (1+η)*(Real.sqrt (1+η)*Real.sqrt x) = s*Real.sqrt x := by field_simp
      _ ≤ _ := hc
  · apply hhigh.trans
    apply (div_le_iff₀ hroot).mpr
    have he : (s+1/Real.sqrt x)*Real.sqrt x=s*Real.sqrt x+1 := by field_simp
    rw [he]
    exact hcl.le

private lemma product_norm_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ) :
    ‖∏ i ∈ S, (1+z i)‖ ≤ Real.exp (∑ i ∈ S, ‖z i‖) := by
  rw [norm_prod]
  apply le_trans _ (Real.prod_one_add_le_exp_sum S (fun i => norm_nonneg (z i)))
  apply Finset.prod_le_prod (fun i hi => norm_nonneg _)
  intro i hi
  simpa only [norm_one] using norm_add_le (1:ℂ) (z i)

private lemma product_exp_error {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) :
    ‖(∏ i ∈ S, (1+z i))-Complex.exp (∑ i ∈ S, z i)‖ ≤
      Real.exp (∑ i ∈ S, ‖z i‖) * (∑ i ∈ S, ‖z i‖^2) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert a S ha ih =>
    have ih' := ih (fun i hi => hz i (mem_insert_of_mem hi))
    have hza := hz a (mem_insert_self _ _)
    have hfirst : ‖1+z a‖ ≤ Real.exp ‖z a‖ := by
      calc
        ‖1+z a‖ ≤ 1+‖z a‖ := by simpa only [norm_one] using norm_add_le (1:ℂ) (z a)
        _ ≤ Real.exp ‖z a‖ := by simpa only [add_comm] using Real.add_one_le_exp ‖z a‖
    have herror : ‖(1+z a)-Complex.exp (z a)‖ ≤ ‖z a‖^2 := by
      rw [norm_sub_rev]
      calc
        _ = ‖Complex.exp (z a)-1-z a‖ := by congr 1; ring
        _ ≤ _ := Complex.norm_exp_sub_one_sub_id_le hza
    have htail : ‖Complex.exp (∑ i ∈ S,z i)‖ ≤ Real.exp (∑ i ∈ S, ‖z i‖) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_sum_le _ _))
    have hsplit : (∏ i ∈ insert a S,(1+z i))-Complex.exp (∑ i ∈ insert a S,z i) =
        (1+z a)*((∏ i ∈ S,(1+z i))-Complex.exp (∑ i ∈ S,z i))+
          ((1+z a)-Complex.exp (z a))*Complex.exp (∑ i ∈ S,z i) := by
      rw [prod_insert ha,sum_insert ha,Complex.exp_add]
      ring
    have hsquares : 0 ≤ ∑ i ∈ S, ‖z i‖^2 := sum_nonneg (fun i hi => sq_nonneg _)
    have heone : 1 ≤ Real.exp ‖z a‖ := Real.one_le_exp (norm_nonneg _)
    rw [hsplit,sum_insert ha,sum_insert ha,Real.exp_add]
    calc
      _ ≤ ‖1+z a‖ * ‖(∏ i ∈ S,(1+z i))-Complex.exp (∑ i ∈ S,z i)‖+
          ‖(1+z a)-Complex.exp (z a)‖*‖Complex.exp (∑ i ∈ S,z i)‖ := by
            simpa only [norm_mul] using norm_add_le
              ((1+z a)*((∏ i ∈ S,(1+z i))-Complex.exp (∑ i ∈ S,z i)))
              (((1+z a)-Complex.exp (z a))*Complex.exp (∑ i ∈ S,z i))
      _ ≤ Real.exp ‖z a‖*(Real.exp (∑ i ∈ S, ‖z i‖)*(∑ i ∈ S, ‖z i‖^2))+
          ‖z a‖^2*Real.exp (∑ i ∈ S, ‖z i‖) :=
        add_le_add (mul_le_mul hfirst ih' (norm_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul herror htail (norm_nonneg _) (sq_nonneg _))
      _ ≤ Real.exp ‖z a‖*(Real.exp (∑ i ∈ S, ‖z i‖)*(∑ i ∈ S, ‖z i‖^2))+
          Real.exp ‖z a‖*(‖z a‖^2*Real.exp (∑ i ∈ S, ‖z i‖)) := by
        apply add_le_add_right
        exact le_mul_of_one_le_left (by positivity) heone
      _ = _ := by ring

private def primeWave (p : ℕ) (t : ℝ) : ℂ :=
  (((Real.sqrt p)⁻¹:ℝ):ℂ)*Complex.exp ((-(t*Real.log p):ℝ)*Complex.I)

private lemma primeWave_norm (p : ℕ) (t : ℝ) :
    ‖primeWave p t‖ = (Real.sqrt p)⁻¹ := by
  unfold primeWave
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_sub,neg_zero,Real.exp_zero,mul_one]

private lemma cluster_log_width {η x y : ℝ} (hη : 0 ≤ η) (hx : 0 < x)
    (hxy : x ≤ y) (hy : y ≤ (1+η)*x) :
    |Real.log y-Real.log x| ≤ Real.log (1+η) := by
  have hy0 := hx.trans_le hxy
  have hlo := Real.log_le_log hx hxy
  have hhi := Real.log_le_log hy0 hy
  rw [Real.log_mul (by positivity : (1+η) ≠ 0) hx.ne'] at hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

private lemma cluster_phase_error {η x : ℝ} (hη : 0 ≤ η) (hx : 0 < x)
    (A : Finset ℕ) (hA : ∀ p ∈ A, x < (p:ℝ) ∧ (p:ℝ) ≤ (1+η)*x) (t : ℝ) :
    ‖(∑ p ∈ A, primeWave p t)-((∑ p ∈ A,(Real.sqrt p)⁻¹:ℝ):ℂ)*
        Complex.exp ((-(t*Real.log x):ℝ)*Complex.I)‖ ≤
      (∑ p ∈ A,(Real.sqrt p)⁻¹)*|t| * Real.log (1+η) := by
  rw [Complex.ofReal_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ A, (Real.sqrt p)⁻¹*(|t| * Real.log (1+η)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := cluster_log_width hη hx (hA p hp).1.le (hA p hp).2
      have he : primeWave p t-(((Real.sqrt p)⁻¹:ℝ):ℂ)*
          Complex.exp ((-(t*Real.log x):ℝ)*Complex.I) =
          (((Real.sqrt p)⁻¹:ℝ):ℂ)*(Complex.exp ((-(t*Real.log p):ℝ)*Complex.I)-
            Complex.exp ((-(t*Real.log x):ℝ)*Complex.I)) := by unfold primeWave; ring
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      calc
        _ ≤ |-(t*Real.log p)-(-(t*Real.log x))| := norm_exp_sub_exp_le _ _
        _ = |t| * |Real.log p-Real.log x| := by
          rw [show -(t*Real.log p)-(-(t*Real.log x)) = -t*(Real.log p-Real.log x) by ring,
            abs_mul,abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

private lemma cluster_square_weights {x : ℝ} (hx : 0 < x) (A : Finset ℕ)
    (hA : ∀ p ∈ A, x ≤ (p:ℝ)) :
    (∑ p ∈ A, ((Real.sqrt p)⁻¹)^2) ≤ (∑ p ∈ A,(Real.sqrt p)⁻¹)/Real.sqrt x := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hw := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hx)
    (Real.sqrt_le_sqrt (hA p hp))
  simpa only [one_div,pow_two,div_eq_mul_inv,one_mul] using
    mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (Real.sqrt_nonneg (p:ℝ)))

private def clusterGate (c θ : ℝ) : ℝ := max 0 (-Real.cos θ-c)

private lemma clusterGate_continuous (c : ℝ) : Continuous (clusterGate c) := by
  unfold clusterGate
  fun_prop

private lemma clusterGate_periodic (c : ℝ) : Function.Periodic (clusterGate c) (2*Real.pi) := by
  intro θ
  simp only [clusterGate,Real.cos_add_two_pi]

private lemma clusterGate_bounds {c : ℝ} (hc : 0 ≤ c) (θ : ℝ) :
    0 ≤ clusterGate c θ ∧ clusterGate c θ ≤ 1 := by
  refine ⟨le_max_left _ _,max_le zero_le_one ?_⟩
  linarith [Real.neg_one_le_cos θ]

private lemma clusterGate_mean_pos {c : ℝ} (hc : c < 1) :
    0 < ∫ θ in (0:ℝ)..2*Real.pi, clusterGate c θ := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0:ℝ) < 2*Real.pi by positivity) continuous_const.continuousOn
    (clusterGate_continuous c).continuousOn
    (fun θ hθ => le_max_left 0 (-Real.cos θ-c))
    (show ∃ θ ∈ Icc (0:ℝ) (2*Real.pi), (0:ℝ) < clusterGate c θ from
      ⟨Real.pi,⟨Real.pi_pos.le,by linarith [Real.pi_pos]⟩,
        by simp only [clusterGate,Real.cos_pi,neg_neg]; exact lt_max_of_lt_right (by linarith)⟩)
  simpa only [intervalIntegral.integral_zero] using h

private lemma clusterGate_integer_periods (c : ℝ) {d : ℝ} (hd : 0 < d)
    {n : ℕ} (hn : 0 < n) :
    (∫ t in (0:ℝ)..d, clusterGate c ((2*Real.pi*n/d)*t)) =
      d/(2*Real.pi)*(∫ θ in (0:ℝ)..2*Real.pi, clusterGate c θ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hfreq : 0 < 2*Real.pi*n/d := by positivity
  rw [intervalIntegral.integral_comp_mul_left _ hfreq.ne']
  have hper := (clusterGate_periodic c).intervalIntegral_add_zsmul_eq (n:ℤ) 0
    (fun a b => (clusterGate_continuous c).intervalIntegrable a b)
  simp only [zero_add,zsmul_eq_mul,Int.cast_natCast] at hper
  have he : (2*Real.pi*n/d)*d = (n:ℝ)*(2*Real.pi) := by field_simp
  rw [mul_zero,he,hper,smul_eq_mul]
  field_simp

private def clusterCos (α θ β : ℝ) : ℝ := Real.cos θ+α*Real.cos (θ+β)

private lemma clusterCos_sq (α θ β : ℝ) :
    (clusterCos α θ β)^2+(Real.sin θ+α*Real.sin (θ+β))^2 =
      1+α^2+2*α*Real.cos β := by
  unfold clusterCos
  rw [Real.cos_add,Real.sin_add]
  calc
    _ = (Real.sin θ^2+Real.cos θ^2)*
      ((1+α*Real.cos β)^2+(α*Real.sin β)^2) := by ring
    _ = 1+α^2*(Real.sin β^2+Real.cos β^2)+2*α*Real.cos β := by
      rw [Real.sin_sq_add_cos_sq θ]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq β]; ring

private lemma clusterCos_lower {α : ℝ} (hα : 0 ≤ α) (θ β : ℝ) :
    -(1+α) ≤ clusterCos α θ β := by
  have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (θ+β)) hα
  unfold clusterCos
  linarith [Real.neg_one_le_cos θ]

private lemma clusterCos_negative_region {α : ℝ} (hα : 0 ≤ α) {θ β : ℝ}
    (hβ : Real.cos β ≤ 0) : -Real.sqrt (1+α^2) ≤ clusterCos α θ β := by
  have hsq := clusterCos_sq α θ β
  have hαβ : α*Real.cos β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hβ
  have hroot := Real.sqrt_nonneg (1+α^2)
  have hroot_sq := Real.sq_sqrt (show 0 ≤ 1+α^2 by positivity)
  nlinarith only [hsq,hαβ,hroot,hroot_sq,sq_nonneg (Real.sin θ+α*Real.sin (θ+β))]

private lemma clusterCos_gate {α c b θ β : ℝ} (hα : 0 ≤ α)
    (hb : b ≤ (1+α)*c-α*|β|) (hgate : 0 < clusterGate c θ) :
    clusterCos α θ β ≤ -b := by
  have hθ : Real.cos θ < -c := by
    have h := (lt_max_iff.mp hgate).resolve_left (lt_irrefl (0:ℝ))
    linarith
  have hdiff := Real.abs_cos_sub_cos_le (θ+β) θ
  rw [add_sub_cancel_left] at hdiff
  have hupper : Real.cos (θ+β) ≤ Real.cos θ+|β| := by
    linarith [(le_abs_self (Real.cos (θ+β)-Real.cos θ)).trans hdiff]
  have hm := mul_le_mul_of_nonneg_left hupper hα
  have hm' := mul_le_mul_of_nonneg_left hθ.le (show 0 ≤ 1+α by positivity)
  unfold clusterCos
  nlinarith only [hb,hm,hm']

private def clusterModel (s α ω freq t : ℝ) : ℝ :=
  Real.exp (-2*s*clusterCos α (freq*t) (ω*t))

private lemma clusterModel_bound {s α : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (ω freq t : ℝ) : clusterModel s α ω freq t ≤ Real.exp (2*s*(1+α)) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (clusterCos_lower hα (freq*t) (ω*t)) (by positivity : 0 ≤ 2*s)
  linarith

private lemma clusterModel_negative_bound {s α : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    {ω freq t : ℝ} (ht : Real.cos (ω*t) ≤ 0) :
    clusterModel s α ω freq t ≤ Real.exp (2*s*Real.sqrt (1+α^2)) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (clusterCos_negative_region hα (θ := freq*t) ht)
    (by positivity : 0 ≤ 2*s)
  linarith

private lemma clusterModel_gate_lower {s α c b ω freq t : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hb : b ≤ (1+α)*c-α*|ω*t|) :
    Real.exp (2*s*b)*clusterGate c (freq*t) ≤ clusterModel s α ω freq t := by
  by_cases hg : 0 < clusterGate c (freq*t)
  · have h := clusterCos_gate hα hb hg
    calc
      _ ≤ Real.exp (2*s*b)*1 := mul_le_mul_of_nonneg_left
        (clusterGate_bounds hc (freq*t)).2 (Real.exp_pos _).le
      _ ≤ _ := by
        rw [mul_one]
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*s)
        linarith
  · have he : clusterGate c (freq*t)=0 := le_antisymm (le_of_not_gt hg) (clusterGate_bounds hc _).1
    rw [he,mul_zero]
    exact (Real.exp_pos _).le

private lemma cluster_primeWave_euler {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeWave p t = Complex.exp ((1/2-(1+(t:ℂ)*Complex.I))*(Real.log p:ℂ)) := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hroot : (Real.sqrt p:ℂ) = Complex.exp ((Real.log p:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hpR,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [primeWave,Complex.ofReal_inv,hroot,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma cluster_euler_product (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (t : ℝ) :
    divisorCoreMellinEuler P (1+(t:ℂ)*Complex.I) = ∏ p ∈ P,(1-primeWave p t) := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [cluster_primeWave_euler (hP p hp)]

private lemma cluster_unit_one_pos :
    0 < (mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-1)).re := by
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x:ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x:ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  have hk (x : ℝ) : (x:ℂ)^((-1:ℂ)-1) • (divisorContinuousUnitHead x:ℂ) =
      ((divisorContinuousUnitHead x/x^2:ℝ):ℂ) := by
    rw [show (-1:ℂ)-1=-(2:ℂ) by norm_num,Complex.cpow_neg]
    norm_num only [Complex.cpow_ofNat,smul_eq_mul]
    push_cast
    ring
  have hi := mellinConvergent_mobiusDivisorContinuousHead ∅ (s := 1) (by norm_num)
  rw [hempty] at hi
  change IntegrableOn (fun x : ℝ => (x:ℂ)^((-1:ℂ)-1) • (divisorContinuousUnitHead x:ℂ)) (Ioi 0) at hi
  simp_rw [hk] at hi
  have hir : IntegrableOn (fun x : ℝ => divisorContinuousUnitHead x/x^2) (Ioi 0) := by
    simpa only [IntegrableOn,RCLike.re_to_complex,Complex.ofReal_re] using hi.re
  have hp : 0 < ∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^2 := by
    apply (integral_pos_iff_support_of_nonneg_ae _ hir).mpr
    · have hsub : Ioo (1:ℝ) 2 ⊆ Function.support (fun x => divisorContinuousUnitHead x/x^2) := by
        intro x hx
        exact ne_of_gt (div_pos (divisorContinuousUnitHead_pos_first hx) (sq_pos_of_pos (by linarith [hx.1])))
      apply lt_of_lt_of_le _ (measure_mono hsub)
      rw [Measure.restrict_apply measurableSet_Ioo]
      have he : Ioo (1:ℝ) 2 ∩ Ioi 0 = Ioo (1:ℝ) 2 :=
        inter_eq_left.mpr (fun x hx => by change 0 < x; linarith [hx.1])
      rw [he,Real.volume_Ioo]
      norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact div_nonneg (divisorContinuousUnitHead_nonneg x) (sq_nonneg _)
  rw [mellin]
  simp_rw [hk]
  rw [integral_complex_ofReal,Complex.ofReal_re]
  exact hp

private def clusterMellin (P : Finset ℕ) (t : ℝ) : ℂ :=
  mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) (-(1+(t:ℂ)*Complex.I))

private lemma clusterMellin_zero_ne (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    clusterMellin P 0 ≠ 0 := by
  have hEuler : divisorCoreMellinEuler P 1 ≠ 0 := by
    have he := cluster_euler_product P hP 0
    simp only [Complex.ofReal_zero,zero_mul,add_zero] at he
    rw [he]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    have hroot : 1 < Real.sqrt p := by
      simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hp1
    have hw := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 1) hroot
    simp only [one_div,inv_one] at hw
    intro heq
    have hz : primeWave p 0=1 := by linear_combination -heq
    have hn := primeWave_norm p 0
    rw [hz,norm_one] at hn
    linarith
  have hunit : mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-1) ≠ 0 := by
    intro h
    have hp := cluster_unit_one_pos
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl _ hp)
  dsimp [clusterMellin]
  simp only [zero_mul,add_zero]
  rw [mellin_mobiusDivisorContinuousHead_euler P hP (s := 1) (by norm_num)]
  exact mul_ne_zero hEuler hunit

private lemma clusterMellin_continuous (P : Finset ℕ) : Continuous (clusterMellin P) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := (differentiableAt_mellin_mobiusDivisorContinuousHead P
    (s := 1+(t:ℂ)*Complex.I) (by simp; norm_num)).continuousAt
  exact h.comp (f := fun u : ℝ => 1+(u:ℂ)*Complex.I) (x := t) (by fun_prop)

private def clusterWeight (P : Finset ℕ) (t : ℝ) : ℝ := ‖clusterMellin P t‖^2

private lemma clusterWeight_continuous (P : Finset ℕ) : Continuous (clusterWeight P) :=
  (clusterMellin_continuous P).norm.pow 2

private lemma clusterWeight_zero_pos (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    0 < clusterWeight P 0 := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (clusterMellin_zero_ne P hP))

private lemma clusterWeight_pair (P : Finset ℕ) (hP : P.Nonempty)
    (hPrime : ∀ p ∈ P,p.Prime) (t : ℝ) :
    divisorCoreMellinPair P (1+(t:ℂ)*Complex.I) = (clusterWeight P t:ℂ) := by
  have hfirst := mellin_mobiusDivisorContinuousHead_eq_core P hP hPrime
    (s := 1+(t:ℂ)*Complex.I) (by simp; norm_num)
  have hsecond := mellin_mobiusDivisorContinuousHead_eq_core P hP hPrime
    (s := 2-(1+(t:ℂ)*Complex.I)) (by simp; norm_num)
  have hconj := mellin_conj_of_conj_invariant
    (F := fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ))
    (by intro x; simp) (-(1+(t:ℂ)*Complex.I))
  have he : (starRingEnd ℂ) (-(1+(t:ℂ)*Complex.I)) = -(2-(1+(t:ℂ)*Complex.I)) := by
    simp
    ring
  rw [he,hsecond] at hconj
  rw [divisorCoreMellinPair,← hfirst,hconj,Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  rfl

private lemma clusterWeight_integrable (P : Finset ℕ) (hP : P.Nonempty)
    (hPrime : ∀ p ∈ P,p.Prime) : Integrable (clusterWeight P) := by
  have hi := integrable_exp_mul_divisorCoreMellinPair_one P hP 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,
    clusterWeight_pair P hP hPrime] at hi
  simpa only [RCLike.re_to_complex,Complex.ofReal_re] using hi.re

private lemma cluster_model_parameters {α : ℝ} (hα : 0 < α) (ω : ℝ)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : 0 < w 0) :
    ∃ c b m d : ℝ, 0 ≤ c ∧ c < 1 ∧ Real.sqrt (1+α^2) < b ∧ 0 < m ∧ 0 < d ∧
      ∀ t ∈ Icc (0:ℝ) d, m ≤ w t ∧ 1/2 ≤ Real.cos (ω*t) ∧
        b ≤ (1+α)*c-α*|ω*t| := by
  let A := 1+α
  let k := Real.sqrt (1+α^2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hkA : k < A := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1+α^2 by positivity)
    dsimp [k,A] at *
    nlinarith only [hsq,hα,hk]
  let b := (k+A)/2
  have hkb : k < b := by dsimp [b]; linarith
  have hbA : b < A := by dsimp [b]; linarith
  have hb : 0 < b := hk.trans_lt hkb
  let c := (b+A)/(2*A)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by
    apply (div_lt_one (show 0 < 2*A by positivity)).mpr
    linarith
  have hAc : A*c = (b+A)/2 := by dsimp [c]; field_simp
  have hgap : b < A*c := by rw [hAc]; linarith
  let m := w 0/2
  have hm : 0 < m := by dsimp [m]; positivity
  have hwm : m < w 0 := by dsimp [m]; linarith
  have hcoscont : Continuous (fun t : ℝ => Real.cos (ω*t)) := by fun_prop
  have hgapcont : Continuous (fun t : ℝ => (1+α)*c-α*|ω*t|) := by fun_prop
  have hwe := hw.continuousAt.eventually (eventually_gt_nhds hwm)
  have hce := hcoscont.continuousAt.eventually
    (eventually_gt_nhds (show (1/2:ℝ) < Real.cos (ω*0) by norm_num))
  have hge := hgapcont.continuousAt.eventually
    (eventually_gt_nhds (show b < (1+α)*c-α*|ω*0| by simpa [A] using hgap))
  have he : ∀ᶠ t : ℝ in 𝓝 0, m < w t ∧ 1/2 < Real.cos (ω*t) ∧
      b < (1+α)*c-α*|ω*t| := by
    filter_upwards [hwe,hce,hge] with t ht hc hg
    exact ⟨ht,hc,hg⟩
  obtain ⟨e,he,hlocal⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨c,b,m,e/2,hc,hc1,hkb,hm,by positivity,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htd : dist t 0 < e := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ht0]
    linarith [ht.2]
  exact ⟨(hlocal htd).1.le,(hlocal htd).2.1.le,(hlocal htd).2.2.le⟩

private lemma clusterModel_integrable {s α : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (ω freq : ℝ) (w : ℝ → ℝ) (hw : Integrable w) :
    Integrable (fun t => w t*Real.cos (ω*t)*clusterModel s α ω freq t) := by
  have hc : Continuous (fun t => Real.cos (ω*t)*clusterModel s α ω freq t) := by
    unfold clusterModel clusterCos
    fun_prop
  have hi := hw.mul_bdd hc.aestronglyMeasurable
    (c := Real.exp (2*s*(1+α))) (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_mul,
        abs_of_pos (show 0 < clusterModel s α ω freq t from Real.exp_pos _)]
      exact (mul_le_mul (Real.abs_cos_le_one _) (clusterModel_bound hs hα ω freq t)
        (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)))
  simpa only [mul_assoc] using hi

private lemma clusterModel_global_lower {s α : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (ω freq : ℝ) (w : ℝ → ℝ) (hw : ∀ t,0 ≤ w t) (t : ℝ) :
    -w t*Real.exp (2*s*Real.sqrt (1+α^2)) ≤
      w t*Real.cos (ω*t)*clusterModel s α ω freq t := by
  by_cases ht : 0 ≤ Real.cos (ω*t)
  · calc
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hw t)) (Real.exp_pos _).le
      _ ≤ _ := mul_nonneg (mul_nonneg (hw t) ht) (Real.exp_pos _).le
  · have ht' : Real.cos (ω*t) ≤ 0 := (lt_of_not_ge ht).le
    have hcos : -w t ≤ w t*Real.cos (ω*t) := by
      have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (ω*t)) (hw t)
      linarith
    calc
      _ ≤ (w t*Real.cos (ω*t))*Real.exp (2*s*Real.sqrt (1+α^2)) :=
        mul_le_mul_of_nonneg_right hcos (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonpos_left (clusterModel_negative_bound hs hα ht')
        (mul_nonpos_of_nonneg_of_nonpos (hw t) ht')

private lemma clusterModel_integral_lower {s α c b m d : ℝ}
    (hs : 0 ≤ s) (hα : 0 ≤ α) (hc : 0 ≤ c) (hm : 0 < m) (hd : 0 < d)
    (ω : ℝ) (w : ℝ → ℝ) (hwi : Integrable w) (hw : ∀ t,0 ≤ w t)
    (hlocal : ∀ t ∈ Icc (0:ℝ) d, m ≤ w t ∧ 1/2 ≤ Real.cos (ω*t) ∧
      b ≤ (1+α)*c-α*|ω*t|) {n : ℕ} (hn : 0 < n) :
    (m/2)*Real.exp (2*s*b)*(d/(2*Real.pi)*(∫ θ in (0:ℝ)..2*Real.pi, clusterGate c θ))-
        (∫ t,w t)*Real.exp (2*s*Real.sqrt (1+α^2)) ≤
      ∫ t,w t*Real.cos (ω*t)*clusterModel s α ω (2*Real.pi*n/d) t := by
  classical
  let freq := 2*Real.pi*n/d
  let G := (Ioc (0:ℝ) d).indicator (fun t => clusterGate c (freq*t))
  have hgcont : Continuous (fun t => clusterGate c (freq*t)) :=
    (clusterGate_continuous c).comp (by fun_prop)
  have hgi : Integrable G :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hgcont.intervalIntegrable 0 d).1
  have hfi := clusterModel_integrable hs hα ω freq w hwi
  have hleft := (hgi.const_mul ((m/2)*Real.exp (2*s*b))).sub
    (hwi.mul_const (Real.exp (2*s*Real.sqrt (1+α^2))))
  have hp : ∀ t, (m/2)*Real.exp (2*s*b)*G t-w t*Real.exp (2*s*Real.sqrt (1+α^2)) ≤
      w t*Real.cos (ω*t)*clusterModel s α ω freq t := by
    intro t
    by_cases ht : t ∈ Ioc (0:ℝ) d
    · have hl := hlocal t ⟨ht.1.le,ht.2⟩
      have hcoef : m/2 ≤ w t*Real.cos (ω*t) := by
        calc
          m/2 = m*(1/2) := by ring
          _ ≤ _ := mul_le_mul hl.1 hl.2.1 (by norm_num) (hw t)
      have hgate := clusterModel_gate_lower hs hα hc hl.2.2 (freq := freq)
      have hpos : (m/2)*Real.exp (2*s*b)*G t ≤
          w t*Real.cos (ω*t)*clusterModel s α ω freq t := by
        rw [show G t=clusterGate c (freq*t) from Set.indicator_of_mem ht _]
        calc
          _ = (m/2)*(Real.exp (2*s*b)*clusterGate c (freq*t)) := by ring
          _ ≤ (m/2)*clusterModel s α ω freq t := mul_le_mul_of_nonneg_left hgate (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      exact (sub_le_self _ (mul_nonneg (hw t) (Real.exp_pos _).le)).trans hpos
    · rw [show G t=0 from Set.indicator_of_notMem ht _,mul_zero,zero_sub,← neg_mul]
      exact clusterModel_global_lower hs hα ω freq w hw t
  have hi := integral_mono hleft hfi hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hgi.const_mul _) (hwi.mul_const _),integral_const_mul,integral_mul_const] at hi
  have hG : (∫ t,G t) = d/(2*Real.pi)*(∫ θ in (0:ℝ)..2*Real.pi,clusterGate c θ) := by
    rw [integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hd.le]
    exact clusterGate_integer_periods c hd hn
  rw [hG] at hi
  exact hi

private lemma exists_positive_cluster_model {α : ℝ} (hα : 0 < α) (ω : ℝ)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwi : Integrable w)
    (hw : ∀ t,0 ≤ w t) (hw0 : 0 < w 0) :
    ∃ s d g : ℝ, 0 < s ∧ 0 < d ∧ 0 < g ∧ ∀ n : ℕ, 0 < n →
      g ≤ ∫ t,w t*Real.cos (ω*t)*clusterModel s α ω (2*Real.pi*n/d) t := by
  obtain ⟨c,b,m,d,hc,hc1,hkb,hm,hd,hlocal⟩ := cluster_model_parameters hα ω w hwc hw0
  let k := Real.sqrt (1+α^2)
  let C := (m/2)*(d/(2*Real.pi)*(∫ θ in (0:ℝ)..2*Real.pi,clusterGate c θ))
  let W := ∫ t,w t
  have hC : 0 < C := by
    have hg := clusterGate_mean_pos hc1
    dsimp [C]
    positivity
  have hrate : 0 < 2*(b-k) := by dsimp [k]; linarith
  have hexp : Tendsto (fun s : ℝ => C*Real.exp (2*(b-k)*s)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hrate)).const_mul_atTop hC
  obtain ⟨s,hlarge,hs⟩ := ((hexp.eventually (eventually_gt_atTop W)).and
    (eventually_gt_atTop (0:ℝ))).exists
  let g := C*Real.exp (2*s*b)-W*Real.exp (2*s*k)
  have hg : 0 < g := by
    have hp := mul_pos (sub_pos.mpr hlarge) (Real.exp_pos (2*s*k))
    have he : Real.exp (2*s*b) = Real.exp (2*(b-k)*s)*Real.exp (2*s*k) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [g]
    rw [he]
    nlinarith only [hp]
  refine ⟨s,d,g,hs,hd,hg,?_⟩
  intro n hn
  calc
    g = (m/2)*Real.exp (2*s*b)*(d/(2*Real.pi)*(∫ θ in (0:ℝ)..2*Real.pi,clusterGate c θ))-
      (∫ t,w t)*Real.exp (2*s*Real.sqrt (1+α^2)) := by dsimp [g,C,W,k]; ring
    _ ≤ _ := clusterModel_integral_lower hs.le hα.le hc hm hd ω w hwi hw hlocal hn

private def clusterEta (r : ℝ) (n : ℕ) : ℝ := (r-1)/(2*((n:ℝ)+1))
private def clusterScale (d : ℝ) (n : ℕ) : ℝ := Real.exp (2*Real.pi*n/d)

private lemma clusterEta_pos {r : ℝ} (hr : 1 < r) (n : ℕ) : 0 < clusterEta r n := by
  unfold clusterEta
  positivity

private lemma clusterEta_separated {r : ℝ} (hr : 1 < r) (n : ℕ) : 1+clusterEta r n < r := by
  have h : clusterEta r n ≤ (r-1)/2 := by
    unfold clusterEta
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

private lemma clusterEta_tendsto (r : ℝ) : Tendsto (clusterEta r) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((r-1)/2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with n
  dsimp [clusterEta]
  field_simp

private lemma clusterScale_tendsto {d : ℝ} (hd : 0 < d) : Tendsto (clusterScale d) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (2*Real.pi/d)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  apply (Real.tendsto_exp_atTop.comp h).congr'
  filter_upwards with n
  dsimp [clusterScale]
  congr 1
  ring

private lemma exists_quantized_prime_clusters {s r d : ℝ} (hs : 0 < s) (hr : 1 < r) (hd : 0 < d) :
    ∃ N : ℕ → ℕ, ∃ A B : ℕ → Finset ℕ, ∀ n : ℕ,
      n+1 ≤ N n ∧
      (A n).card=⌈s*Real.sqrt (clusterScale d (N n))⌉₊ ∧
      (B n).card=⌈s*Real.sqrt (clusterScale d (N n))⌉₊ ∧ Disjoint (A n) (B n) ∧
      (∀ p ∈ A n,p.Prime ∧ clusterScale d (N n) < (p:ℝ) ∧
        (p:ℝ) ≤ (1+clusterEta r n)*clusterScale d (N n)) ∧
      (∀ p ∈ B n,p.Prime ∧ r*clusterScale d (N n) < (p:ℝ) ∧
        (p:ℝ) ≤ (1+clusterEta r n)*(r*clusterScale d (N n))) := by
  have hfor (n : ℕ) : ∃ k : ℕ, ∃ A B : Finset ℕ,
      n+1 ≤ k ∧ A.card=⌈s*Real.sqrt (clusterScale d k)⌉₊ ∧
      B.card=⌈s*Real.sqrt (clusterScale d k)⌉₊ ∧ Disjoint A B ∧
      (∀ p ∈ A,p.Prime ∧ clusterScale d k < (p:ℝ) ∧ (p:ℝ) ≤ (1+clusterEta r n)*clusterScale d k) ∧
      (∀ p ∈ B,p.Prime ∧ r*clusterScale d k < (p:ℝ) ∧ (p:ℝ) ≤ (1+clusterEta r n)*(r*clusterScale d k)) := by
    have hsupply := paired_cluster_supply (clusterEta_pos hr n) hs (clusterEta_separated hr n)
    have he := ((clusterScale_tendsto hd).eventually hsupply).and (eventually_ge_atTop (n+1))
    obtain ⟨k,hcap,hk⟩ := he.exists
    obtain ⟨A,B,hA,hB,hdj,hpA,hpB⟩ := hcap
    exact ⟨k,A,B,hk,hA,hB,hdj,hpA,hpB⟩
  choose N A B h using hfor
  exact ⟨N,A,B,h⟩

private lemma cluster_phase_norm (x t : ℝ) :
    ‖Complex.exp ((-(t*Real.log x):ℝ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,zero_sub,neg_zero,Real.exp_zero]

private lemma cluster_mass_tendsto {s : ℝ} (hs : 0 < s)
    (eta X : ℕ → ℝ) (A : ℕ → Finset ℕ)
    (he0 : ∀ n,0 ≤ eta n) (he : Tendsto eta atTop (𝓝 0))
    (hX1 : ∀ n,1 ≤ X n) (hX : Tendsto X atTop atTop)
    (hcard : ∀ n,(A n).card=⌈s*Real.sqrt (X n)⌉₊)
    (hA : ∀ n,∀ p ∈ A n,X n < (p:ℝ) ∧ (p:ℝ) ≤ (1+eta n)*X n) :
    Tendsto (fun n => ∑ p ∈ A n,(Real.sqrt p)⁻¹) atTop (𝓝 s) := by
  have hroot : Tendsto (fun n => Real.sqrt (1+eta n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (1+(0:ℝ))).comp (tendsto_const_nhds.add he)
  have hinv : Tendsto (fun n => 1/Real.sqrt (X n)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hX)
  have hlo : Tendsto (fun n => s/Real.sqrt (1+eta n)) atTop (𝓝 s) := by
    have h := (tendsto_const_nhds (x := s)).div hroot (by norm_num : (1:ℝ) ≠ 0)
    rw [div_one] at h
    apply h.congr'
    filter_upwards with n
    rfl
  have hhi : Tendsto (fun n => s+1/Real.sqrt (X n)) atTop (𝓝 s) := by
    simpa using tendsto_const_nhds.add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => (cluster_weight_bounds (he0 n) hs (hX1 n) (A n) (hcard n) (hA n)).1)
    (fun n => (cluster_weight_bounds (he0 n) hs (hX1 n) (A n) (hcard n) (hA n)).2)

private lemma cluster_squares_tendsto {s : ℝ} (hs : 0 < s)
    (eta X : ℕ → ℝ) (A : ℕ → Finset ℕ)
    (he0 : ∀ n,0 ≤ eta n) (he : Tendsto eta atTop (𝓝 0))
    (hX1 : ∀ n,1 ≤ X n) (hX : Tendsto X atTop atTop)
    (hcard : ∀ n,(A n).card=⌈s*Real.sqrt (X n)⌉₊)
    (hA : ∀ n,∀ p ∈ A n,X n < (p:ℝ) ∧ (p:ℝ) ≤ (1+eta n)*X n) :
    Tendsto (fun n => ∑ p ∈ A n,((Real.sqrt p)⁻¹)^2) atTop (𝓝 0) := by
  have hm := cluster_mass_tendsto hs eta X A he0 he hX1 hX hcard hA
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hX)
  have ht : Tendsto (fun n => (∑ p ∈ A n,(Real.sqrt p)⁻¹)/Real.sqrt (X n)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,Function.comp_def] using hm.mul hi
  apply squeeze_zero (fun n => sum_nonneg (fun p hp => sq_nonneg _)) _ ht
  intro n
  exact cluster_square_weights (lt_of_lt_of_le zero_lt_one (hX1 n)) (A n)
    (fun p hp => (hA n p hp).1.le)

private lemma cluster_wave_sum_tendsto {s : ℝ} (hs : 0 < s)
    (eta X : ℕ → ℝ) (A : ℕ → Finset ℕ)
    (he0 : ∀ n,0 ≤ eta n) (he : Tendsto eta atTop (𝓝 0))
    (hX1 : ∀ n,1 ≤ X n) (hX : Tendsto X atTop atTop)
    (hcard : ∀ n,(A n).card=⌈s*Real.sqrt (X n)⌉₊)
    (hA : ∀ n,∀ p ∈ A n,X n < (p:ℝ) ∧ (p:ℝ) ≤ (1+eta n)*X n) (t : ℝ) :
    Tendsto (fun n => (∑ p ∈ A n,primeWave p t)-(s:ℂ)*
      Complex.exp ((-(t*Real.log (X n)):ℝ)*Complex.I)) atTop (𝓝 0) := by
  let mass : ℕ → ℝ := fun n => ∑ p ∈ A n,(Real.sqrt p)⁻¹
  have hm := cluster_mass_tendsto hs eta X A he0 he hX1 hX hcard hA
  have hlog : Tendsto (fun n => Real.log (1+eta n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp
      (show Tendsto (fun n => 1+eta n) atTop (𝓝 1) by simpa using tendsto_const_nhds.add he)
  have hsmall : Tendsto (fun n => mass n*|t| * Real.log (1+eta n)+|mass n-s|) atTop (𝓝 0) := by
    simpa only [mass,mul_zero,sub_self,abs_zero,add_zero,zero_add] using
      ((hm.mul_const |t|).mul hlog).add ((hm.sub (tendsto_const_nhds (x := s))).abs)
  apply squeeze_zero_norm _ hsmall
  intro n
  have hn := cluster_phase_error (he0 n) (lt_of_lt_of_le zero_lt_one (hX1 n)) (A n) (hA n) t
  let ph := Complex.exp ((-(t*Real.log (X n)):ℝ)*Complex.I)
  have hamp : ‖(mass n:ℂ)*ph-(s:ℂ)*ph‖ = |mass n-s| := by
    rw [← sub_mul,norm_mul,show (mass n:ℂ)-(s:ℂ)=((mass n-s:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_eq_abs,cluster_phase_norm,mul_one]
  calc
    _ ≤ ‖(∑ p ∈ A n,primeWave p t)-(mass n:ℂ)*ph‖+‖(mass n:ℂ)*ph-(s:ℂ)*ph‖ :=
      calc
        _ = ‖((∑ p ∈ A n,primeWave p t)-(mass n:ℂ)*ph)+((mass n:ℂ)*ph-(s:ℂ)*ph)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hn hamp.le

private lemma cluster_product_exp_tendsto {ι : Type*} (S : ℕ → Finset ι) (z : ℕ → ι → ℂ)
    {c : ℝ} (hm : Tendsto (fun n => ∑ i ∈ S n, ‖z n i‖) atTop (𝓝 c))
    (hq : Tendsto (fun n => ∑ i ∈ S n, ‖z n i‖^2) atTop (𝓝 0))
    (hz : ∀ n,∀ i ∈ S n, ‖z n i‖ ≤ 1) :
    Tendsto (fun n => (∏ i ∈ S n,(1+z n i))-Complex.exp (∑ i ∈ S n,z n i)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => Real.exp (∑ i ∈ S n, ‖z n i‖)*(∑ i ∈ S n, ‖z n i‖^2))
      atTop (𝓝 0) := by
    have he : Tendsto (fun n => Real.exp (∑ i ∈ S n, ‖z n i‖)) atTop (𝓝 (Real.exp c)) := by
      simpa only [Function.comp_def] using (Real.continuous_exp.tendsto c).comp hm
    simpa only [mul_zero] using he.mul hq
  exact squeeze_zero_norm (fun n => product_exp_error (S n) (z n) (hz n)) hbound

private lemma cluster_exp_difference_tendsto (f g : ℕ → ℂ) {C : ℝ}
    (hfg : Tendsto (fun n => f n-g n) atTop (𝓝 0)) (hg : ∀ n, ‖g n‖ ≤ C) :
    Tendsto (fun n => Complex.exp (f n)-Complex.exp (g n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ‖f n-g n‖) atTop (𝓝 0) := by simpa using hfg.norm
  have he := hn.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hbound : ∀ᶠ n in atTop, ‖Complex.exp (f n)-Complex.exp (g n)‖ ≤
      (2*Real.exp C)*‖f n-g n‖ := by
    filter_upwards [he] with n hn
    have h := Complex.locally_lipschitz_exp zero_le_one le_rfl (g n) (f n) hn
    have hnorm : ‖Complex.exp (g n)‖ ≤ Real.exp C :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hg n))
    calc
      _ ≤ (1+1)*‖Complex.exp (g n)‖*‖f n-g n‖ := h
      _ ≤ _ := by gcongr; norm_num
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero] using hn.const_mul (2*Real.exp C)

private lemma cluster_norm_sq_error {z v : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) (hv : ‖v‖ ≤ C) :
    |‖z‖^2-‖v‖^2| ≤ (2*C)*‖z-v‖ := by
  calc
    _ = |‖z‖-‖v‖| * (‖z‖+‖v‖) := by
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ ‖z-v‖*(2*C) := mul_le_mul (abs_norm_sub_norm_le z v)
      (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private lemma cluster_norm_sq_tendsto (f g : ℕ → ℂ) {C : ℝ}
    (hfg : Tendsto (fun n => f n-g n) atTop (𝓝 0))
    (hf : ∀ᶠ n in atTop, ‖f n‖ ≤ C) (hg : ∀ᶠ n in atTop, ‖g n‖ ≤ C) :
    Tendsto (fun n => ‖f n‖^2-‖g n‖^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ‖f n-g n‖) atTop (𝓝 0) := by simpa using hfg.norm
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hn.const_mul (2*C))
  filter_upwards [hf,hg] with n hf hg
  simpa only [Real.norm_eq_abs] using cluster_norm_sq_error hf hg

private def clusterExponent (s α ω freq t : ℝ) : ℂ :=
  -(s:ℂ)*Complex.exp ((-(freq*t):ℝ)*Complex.I)-
    ((s*α:ℝ):ℂ)*Complex.exp ((-((freq+ω)*t):ℝ)*Complex.I)

private lemma cluster_unit_phase_norm (θ : ℝ) : ‖Complex.exp ((θ:ℂ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma clusterExponent_norm {s α : ℝ} (hs : 0 ≤ s) (hα : 0 ≤ α)
    (ω freq t : ℝ) : ‖clusterExponent s α ω freq t‖ ≤ s+s*α := by
  unfold clusterExponent
  calc
    _ ≤ ‖-(s:ℂ)*Complex.exp ((-(freq*t):ℝ)*Complex.I)‖+
      ‖((s*α:ℝ):ℂ)*Complex.exp ((-((freq+ω)*t):ℝ)*Complex.I)‖ := norm_sub_le _ _
    _ = _ := by
      rw [norm_mul,norm_mul,norm_neg,cluster_unit_phase_norm,cluster_unit_phase_norm,
        mul_one,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg hs,abs_of_nonneg (mul_nonneg hs hα)]

private lemma clusterExponent_model (s α ω freq t : ℝ) :
    ‖Complex.exp (clusterExponent s α ω freq t)‖^2 = clusterModel s α ω freq t := by
  rw [Complex.norm_exp,pow_two,← Real.exp_add]
  unfold clusterModel clusterCos clusterExponent
  congr 1
  simp only [Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.exp_re,Complex.I_re,Complex.I_im,
    Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,
    neg_zero,mul_one,Real.exp_zero,one_mul,Real.cos_neg]
  rw [add_mul]
  ring

private lemma exists_cluster_multiplier_sequence {s r d : ℝ} (hs : 0 < s) (hr : 1 < r) (hd : 0 < d) :
    ∃ N : ℕ → ℕ, ∃ S : ℕ → Finset ℕ, ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      (∀ n,(∑ p ∈ S n,(Real.sqrt p)⁻¹) ≤ W) ∧ (∀ n,n+1 ≤ N n) ∧
      (∀ n,∀ p ∈ S n,p.Prime ∧ clusterScale d (N n) < (p:ℝ)) ∧
      (∀ n (t : ℝ), ‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖ ≤ C) ∧
      (∀ n (t : ℝ), ‖Complex.exp (clusterExponent s (1/Real.sqrt r) (Real.log r)
        (2*Real.pi*N n/d) t)‖ ≤ C) ∧
      (∀ t : ℝ,Tendsto (fun n => ‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖^2-
        clusterModel s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t) atTop (𝓝 0)) := by
  classical
  obtain ⟨N,A,B,hdata⟩ := exists_quantized_prime_clusters hs hr hd
  let eta := clusterEta r
  let X : ℕ → ℝ := fun n => clusterScale d (N n)
  let S : ℕ → Finset ℕ := fun n => A n ∪ B n
  let v : ℝ := s/Real.sqrt r
  let D : ℝ := s+v
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hroot : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hv : 0 < v := div_pos hs hroot
  have he0 (n : ℕ) : 0 ≤ eta n := (clusterEta_pos hr n).le
  have he : Tendsto eta atTop (𝓝 0) := clusterEta_tendsto r
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono
    (fun n => (Nat.le_succ n).trans (hdata n).1) tendsto_id
  have hX : Tendsto X atTop atTop := (clusterScale_tendsto hd).comp hN
  have hX1 (n : ℕ) : 1 ≤ X n := Real.one_le_exp (by positivity)
  have hrX : Tendsto (fun n => r*X n) atTop atTop := hX.const_mul_atTop hr0
  have hrX1 (n : ℕ) : 1 ≤ r*X n := by nlinarith [hX1 n]
  have hcA (n : ℕ) : (A n).card=⌈s*Real.sqrt (X n)⌉₊ := (hdata n).2.1
  have hcB (n : ℕ) : (B n).card=⌈v*Real.sqrt (r*X n)⌉₊ := by
    rw [(hdata n).2.2.1]
    congr 1
    dsimp [v]
    rw [Real.sqrt_mul hr0.le]
    field_simp
    rfl
  have hAB (n : ℕ) : Disjoint (A n) (B n) := (hdata n).2.2.2.1
  have hA (n : ℕ) (p : ℕ) (hp : p ∈ A n) : X n < (p:ℝ) ∧ (p:ℝ) ≤ (1+eta n)*X n :=
    ((hdata n).2.2.2.2.1 p hp).2
  have hB (n : ℕ) (p : ℕ) (hp : p ∈ B n) : r*X n < (p:ℝ) ∧ (p:ℝ) ≤ (1+eta n)*(r*X n) :=
    ((hdata n).2.2.2.2.2 p hp).2
  have hpS (n : ℕ) (p : ℕ) (hp : p ∈ S n) : p.Prime ∧ X n < (p:ℝ) := by
    rcases mem_union.mp hp with hp|hp
    · exact ⟨((hdata n).2.2.2.2.1 p hp).1,(hA n p hp).1⟩
    · refine ⟨((hdata n).2.2.2.2.2 p hp).1,lt_trans ?_ (hB n p hp).1⟩
      nlinarith [hX1 n]
  have hmA := cluster_mass_tendsto hs eta X A he0 he hX1 hX hcA hA
  have hmB := cluster_mass_tendsto hv eta (fun n => r*X n) B he0 he hrX1 hrX hcB hB
  have hqA := cluster_squares_tendsto hs eta X A he0 he hX1 hX hcA hA
  have hqB := cluster_squares_tendsto hv eta (fun n => r*X n) B he0 he hrX1 hrX hcB hB
  have hm : Tendsto (fun n => ∑ p ∈ S n,(Real.sqrt p)⁻¹) atTop (𝓝 D) := by
    simpa only [S,sum_union (hAB _)] using hmA.add hmB
  have hq : Tendsto (fun n => ∑ p ∈ S n,((Real.sqrt p)⁻¹)^2) atTop (𝓝 0) := by
    simpa only [S,sum_union (hAB _),add_zero] using hqA.add hqB
  have hmass (n : ℕ) : (∑ p ∈ S n,(Real.sqrt p)⁻¹) ≤ D+2 := by
    have hi (Y : ℝ) (hY : 1 ≤ Y) : 1/Real.sqrt Y ≤ 1 := by
      have hy : 1 ≤ Real.sqrt Y := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hY
      exact (div_le_one (by positivity : 0 < Real.sqrt Y)).mpr hy
    have hma := (cluster_weight_bounds (he0 n) hs (hX1 n) (A n) (hcA n) (hA n)).2
    have hmb := (cluster_weight_bounds (he0 n) hv (hrX1 n) (B n) (hcB n) (hB n)).2
    dsimp [S,D]
    rw [sum_union (hAB n)]
    linarith [hi (X n) (hX1 n),hi (r*X n) (hrX1 n)]
  have hprod (n : ℕ) (t : ℝ) : ‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖ ≤ Real.exp (D+2) := by
    rw [cluster_euler_product (S n) (fun p hp => (hpS n p hp).1) t]
    have h := product_norm_bound (S n) (fun p => -primeWave p t)
    simp only [norm_neg,primeWave_norm,← sub_eq_add_neg] at h
    exact h.trans (Real.exp_le_exp.mpr (hmass n))
  have hmod (n : ℕ) (t : ℝ) : ‖Complex.exp (clusterExponent s (1/Real.sqrt r) (Real.log r)
      (2*Real.pi*N n/d) t)‖ ≤ Real.exp (D+2) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    have h := clusterExponent_norm hs.le (by positivity : 0 ≤ 1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t
    dsimp [D,v]
    simpa only [mul_one_div] using h.trans (by linarith : s+s*(1/Real.sqrt r) ≤ s+s*(1/Real.sqrt r)+2)
  refine ⟨N,S,Real.exp (D+2),D+2,Real.exp_pos _,by dsimp [D,v]; positivity,
    hmass,fun n => (hdata n).1,hpS,hprod,hmod,?_⟩
  intro t
  have hwA := cluster_wave_sum_tendsto hs eta X A he0 he hX1 hX hcA hA t
  have hwB := cluster_wave_sum_tendsto hv eta (fun n => r*X n) B he0 he hrX1 hrX hcB hB t
  have hsmall : Tendsto (fun n => (∏ p ∈ S n,(1-primeWave p t))-
      Complex.exp (∑ p ∈ S n,-primeWave p t)) atTop (𝓝 0) := by
    apply cluster_product_exp_tendsto (S := S) (z := fun n p => -primeWave p t)
    · simpa only [norm_neg,primeWave_norm] using hm
    · simpa only [norm_neg,primeWave_norm] using hq
    · intro n p hp
      rw [norm_neg,primeWave_norm]
      have hpr : 1 ≤ Real.sqrt p := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((hX1 n).trans (hpS n p hp).2.le)
      simpa only [one_div] using (div_le_one (by positivity : 0 < Real.sqrt p)).mpr hpr
  have hw : Tendsto (fun n => (∑ p ∈ S n,-primeWave p t)-
      clusterExponent s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t) atTop (𝓝 0) := by
    have h := (hwA.add hwB).neg
    simp only [add_zero,neg_zero] at h
    apply h.congr'
    filter_upwards with n
    have hx : Real.log (X n) = 2*Real.pi*N n/d := Real.log_exp _
    have hrx : Real.log (r*X n) = Real.log r+2*Real.pi*N n/d := by
      rw [Real.log_mul hr0.ne' (by linarith [hX1 n] : X n ≠ 0),hx]
    simp only [S,sum_neg_distrib,sum_union (hAB n),hx,hrx,clusterExponent,v,
      mul_one_div,Complex.ofReal_div]
    ring
  have hexp := cluster_exp_difference_tendsto _ _ hw
    (fun n => clusterExponent_norm hs.le (by positivity : 0 ≤ 1/Real.sqrt r)
      (Real.log r) (2*Real.pi*N n/d) t)
  have htotal : Tendsto (fun n => divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)-
      Complex.exp (clusterExponent s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t)) atTop (𝓝 0) := by
    have h := hsmall.add hexp
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards with n
    rw [cluster_euler_product (S n) (fun p hp => (hpS n p hp).1) t]
    ring
  simpa only [clusterExponent_model] using cluster_norm_sq_tendsto _ _ htotal
    (Filter.Eventually.of_forall (fun n => hprod n t)) (Filter.Eventually.of_forall (fun n => hmod n t))

private lemma cluster_euler_continuous (S : Finset ℕ) :
    Continuous (fun t : ℝ => divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)) :=
  (differentiable_divisorCoreMellinEuler S).continuous.comp (by fun_prop)

private lemma cluster_weighted_euler_integrable (S : Finset ℕ) (w : ℝ → ℝ) (ω C : ℝ)
    (hw : Integrable w) (hC : ∀ t : ℝ, ‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖ ≤ C) :
    Integrable (fun t : ℝ => w t*Real.cos (ω*t)*‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2) := by
  have hc : Continuous (fun t : ℝ => Real.cos (ω*t)*‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2) :=
    (show Continuous (fun t : ℝ => Real.cos (ω*t)) by fun_prop).mul
      ((cluster_euler_continuous S).norm.pow 2)
  have hi := hw.mul_bdd hc.aestronglyMeasurable (c := C^2) (Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (sq_nonneg ‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖)]
    have hsq : ‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2 ≤ C^2 := by
      nlinarith [hC t,norm_nonneg (divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I))]
    exact (mul_le_mul (Real.abs_cos_le_one _) hsq (sq_nonneg _) zero_le_one).trans_eq (one_mul _)))
  simpa only [mul_assoc] using hi

private lemma exists_positive_actual_cluster {r : ℝ} (hr : 1 < r)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwi : Integrable w)
    (hw : ∀ t,0 ≤ w t) (hw0 : 0 < w 0) :
    ∃ W : ℝ,0 < W ∧ ∀ L : ℝ,∃ S : Finset ℕ, (∀ p ∈ S,p.Prime ∧ L < (p:ℝ)) ∧
      (∑ p ∈ S,(Real.sqrt p)⁻¹) ≤ W ∧ 0 < ∫ t : ℝ,w t*Real.cos (Real.log r*t)*‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have ha : 0 < 1/Real.sqrt r := by positivity
  obtain ⟨s,d,g,hs,hd,hg,hmodel⟩ := exists_positive_cluster_model ha (Real.log r) w hwc hwi hw hw0
  obtain ⟨N,S,C,W,hC,hW,hmass,hN,hprime,hprod,hmod,hlim⟩ := exists_cluster_multiplier_sequence hs hr hd
  let F : ℕ → ℝ → ℝ := fun n t => w t*Real.cos (Real.log r*t)*
    (‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖^2-
      clusterModel s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t)
  have hdiff (n : ℕ) (t : ℝ) :
      |‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖^2-
        clusterModel s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t| ≤ 2*C^2 := by
    rw [← clusterExponent_model]
    apply abs_sub_le_iff.mpr
    have hp0 := norm_nonneg (divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I))
    have hm0 := norm_nonneg (Complex.exp (clusterExponent s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t))
    constructor <;> nlinarith [hprod n t,hmod n t,sq_nonneg C]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    apply Continuous.aestronglyMeasurable
    have hp := (cluster_euler_continuous (S n)).norm.pow 2
    exact (hwc.mul (by fun_prop)).mul (hp.sub (by unfold clusterModel clusterCos; fun_prop))
  have hbound (n : ℕ) : ∀ᵐ t : ℝ, ‖F n t‖ ≤ w t*(2*C^2) := by
    apply Eventually.of_forall
    intro t
    dsimp [F]
    rw [abs_mul,abs_mul,abs_of_nonneg (hw t)]
    calc
      _ ≤ (w t*1)*(2*C^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw t)) (hdiff n t)
        (abs_nonneg _) (mul_nonneg (hw t) zero_le_one)
      _ = _ := by ring
  have hzero : ∀ᵐ t : ℝ,Tendsto (fun n => F n t) atTop (𝓝 (0:ℝ)) := by
    apply Eventually.of_forall
    intro t
    simpa only [F,mul_zero] using (hlim t).const_mul (w t*Real.cos (Real.log r*t))
  have hint : Tendsto (fun n => ∫ t,F n t) atTop (𝓝 (0:ℝ)) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun t => w t*(2*C^2)) hmeas (hwi.mul_const _) hbound hzero
  have hscale : Tendsto (fun n => clusterScale d (N n)) atTop atTop :=
    (clusterScale_tendsto hd).comp (tendsto_atTop_mono
      (fun n => (Nat.le_succ n).trans (hN n)) tendsto_id)
  refine ⟨W,hW,?_⟩
  intro L
  have hclose := hint.eventually (eventually_gt_nhds (by linarith : -g/2 < (0:ℝ)))
  obtain ⟨n,hn,hlarge⟩ := (hclose.and (hscale.eventually (eventually_gt_atTop L))).exists
  refine ⟨S n,fun p hp => ⟨(hprime n p hp).1,hlarge.trans (hprime n p hp).2⟩,hmass n,?_⟩
  have hpos := hmodel (N n) (lt_of_lt_of_le (Nat.zero_lt_succ n) (hN n))
  have hpint := cluster_weighted_euler_integrable (S n) w (Real.log r) C hwi (hprod n)
  have hmint := clusterModel_integrable hs.le ha.le (Real.log r) (2*Real.pi*N n/d) w hwi
  have he : (∫ t,F n t) =
      (∫ t : ℝ,w t*Real.cos (Real.log r*t)*‖divisorCoreMellinEuler (S n) (1+(t:ℂ)*Complex.I)‖^2)-
      ∫ t,w t*Real.cos (Real.log r*t)*clusterModel s (1/Real.sqrt r) (Real.log r) (2*Real.pi*N n/d) t := by
    rw [← integral_sub hpint hmint]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by dsimp [F]; ring)
  rw [he] at hn
  linarith

private lemma clusterWeight_union (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (hS : ∀ p ∈ S,p.Prime) (hPS : Disjoint P S) (t : ℝ) :
    clusterWeight (P ∪ S) t = clusterWeight P t*‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2 := by
  have hprime : ∀ p ∈ P ∪ S,p.Prime := by
    intro p hp
    exact (mem_union.mp hp).elim (hP p) (hS p)
  dsimp [clusterWeight,clusterMellin]
  rw [mellin_mobiusDivisorContinuousHead_euler (P ∪ S) hprime (by simp; norm_num),
    mellin_mobiusDivisorContinuousHead_euler P hP (by simp; norm_num)]
  have he : divisorCoreMellinEuler (P ∪ S) (1+(t:ℂ)*Complex.I)=
      divisorCoreMellinEuler P (1+(t:ℂ)*Complex.I)*divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I) :=
    Finset.prod_union hPS
  rw [he]
  simp only [norm_mul,mul_pow]
  ring

private lemma cluster_dilation_spectrum (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P,p.Prime) {r : ℝ} (hr : 0 < r) :
    mobiusDivisorDilationMean P r = r/(2*Real.pi)*∫ t,clusterWeight P t*Real.cos (Real.log r*t) := by
  let F : ℝ → ℂ := fun t => Complex.exp ((Real.log r:ℂ)*(1+(t:ℂ)*Complex.I))*
    divisorCoreMellinPair P (1+(t:ℂ)*Complex.I)
  have hi : Integrable F := integrable_exp_mul_divisorCoreMellinPair_one P hP (Real.log r)
  have hre (t : ℝ) : (F t).re = r*(clusterWeight P t*Real.cos (Real.log r*t)) := by
    dsimp [F]
    rw [clusterWeight_pair P hP hprime]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,Complex.exp_re,Complex.add_re,Complex.one_re,Complex.I_re,
      Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_im,mul_one,add_zero,zero_add,
      Real.exp_log hr]
    ring
  have h := congrArg Complex.re (mobiusDivisorDilationMean_eq_contour P hP hprime (Real.log r))
  rw [Real.exp_log hr,divisorCoreMellinContourMean] at h
  have hscalar : (1/(2*(Real.pi:ℂ))) = (((1/(2*Real.pi):ℝ)):ℂ) := by push_cast; rfl
  rw [hscalar] at h
  simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  have hRi : (∫ t,F t).re = ∫ t,(F t).re := (integral_re hi).symm
  change mobiusDivisorDilationMean P r = (1/(2*Real.pi))*(∫ t,F t).re at h
  rw [hRi] at h
  simp_rw [hre] at h
  rw [integral_const_mul] at h
  calc
    _ = (1/(2*Real.pi))*(r*∫ t,clusterWeight P t*Real.cos (Real.log r*t)) := h
    _ = _ := by ring

private lemma prefix_weighted_insertion :
    ∀ P : Finset ℕ,P.Nonempty → (∀ p ∈ P,p.Prime) →
      ∀ r : ℕ,r.Prime → r ∉ P → ∃ W : ℝ,0 < W ∧ ∀ B : ℕ,
      ∃ S : Finset ℕ,(∀ p ∈ S,p.Prime ∧ B < p) ∧ Disjoint P S ∧ r ∉ S ∧ (∑ p ∈ S,(Real.sqrt p)⁻¹) ≤ W ∧
        (∑' n,mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n) <
          (∑' n,mobiusDivisorFixedCoreBlockMass (P ∪ S) n) ∧
        ∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,c*(M:ℝ)^2 ≤
          mobiusDivisorSelectionEnergy M (P ∪ S)-mobiusDivisorSelectionEnergy M (insert r (P ∪ S)) := by
  classical
  intro P hP hprime r hr hrP
  have hrR : (1:ℝ) < r := by exact_mod_cast hr.one_lt
  obtain ⟨W,hW0,hcluster⟩ := exists_positive_actual_cluster hrR (clusterWeight P)
    (clusterWeight_continuous P) (clusterWeight_integrable P hP hprime)
    (fun t => sq_nonneg _) (clusterWeight_zero_pos P hprime)
  refine ⟨W,hW0,?_⟩
  intro B
  let L : ℕ := B+r+P.sup id+1
  obtain ⟨S,hS,hmass,hpositive⟩ := hcluster (L:ℝ)
  have hfresh (p : ℕ) (hp : p ∈ S) : L < p := by exact_mod_cast (hS p hp).2
  have hPS : Disjoint P S := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    have hsup : p ≤ P.sup id := Finset.le_sup (f := id) hp
    have hlt := hfresh p hs
    dsimp [L] at hlt
    omega
  have hrS : r ∉ S := by
    intro hrs
    have hlt := hfresh r hrs
    dsimp [L] at hlt
    omega
  have hSpr : ∀ p ∈ S,p.Prime := fun p hp => (hS p hp).1
  have hQpr : ∀ p ∈ P ∪ S,p.Prime := by
    intro p hp
    exact (mem_union.mp hp).elim (hprime p) (hSpr p)
  have hQ : (P ∪ S).Nonempty := by
    obtain ⟨p,hp⟩ := hP
    exact ⟨p,mem_union_left S hp⟩
  have hrQ : r ∉ P ∪ S := by
    intro h
    exact (mem_union.mp h).elim hrP hrS
  have hW : 0 < mobiusDivisorDilationMean (P ∪ S) r := by
    rw [cluster_dilation_spectrum (P ∪ S) hQ hQpr (by exact_mod_cast hr.pos)]
    apply mul_pos (by positivity)
    have he : (∫ t,clusterWeight (P ∪ S) t*Real.cos (Real.log (r:ℝ)*t)) =
        ∫ t : ℝ,clusterWeight P t*Real.cos (Real.log (r:ℝ)*t)*
          ‖divisorCoreMellinEuler S (1+(t:ℂ)*Complex.I)‖^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [clusterWeight_union P S hprime hSpr hPS]
        ring)
    rw [he]
    exact hpositive
  have hRpr : ∀ p ∈ insert r (P ∪ S),p.Prime := by simpa using And.intro hr hQpr
  have hrelease : 0 < (∑' n,mobiusDivisorFixedCoreBlockMass (P ∪ S) n)-
      ∑' n,mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n := by
    rw [mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean (P ∪ S) hQpr hr hrQ]
    have hprod : 0 < ∏ q ∈ insert r (P ∪ S),(q:ℝ)/(q+1) :=
      prod_pos (fun q hq => div_pos (by exact_mod_cast (hRpr q hq).pos) (by positivity))
    have hdens : 0 < Sieve.squarefreeDensity := by rw [Sieve.squarefreeDensity_eq]; positivity
    have hrpow := Real.rpow_pos_of_pos (show (0:ℝ) < r by exact_mod_cast hr.pos) (-(3/2:ℝ))
    positivity
  refine ⟨S,fun p hp => ⟨hSpr p hp,?_⟩,hPS,hrS,hmass,sub_pos.mp hrelease,?_⟩
  · have hlt := hfresh p hp
    dsimp [L] at hlt
    omega
  · let c := ((∑' n,mobiusDivisorFixedCoreBlockMass (P ∪ S) n)-
      ∑' n,mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n)/2
    have hc : 0 < c := div_pos hrelease (by norm_num)
    refine ⟨c,hc,?_⟩
    have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq (P ∪ S) hQpr).sub
      (tendsto_mobiusDivisorSelectionEnergy_div_sq (insert r (P ∪ S)) hRpr)
    have he := ht.eventually (eventually_gt_nhds (show c < _ by dsimp [c]; linarith))
    filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
    have hMR : (0:ℝ) < M := by exact_mod_cast hM0
    simp only [← sub_div] at hM
    exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

private lemma prefix_inactive (M p : ℕ) (P : Finset ℕ) (hMp : M ≤ p) :
    mobiusDivisorSelectionEnergy M (insert p P)=mobiusDivisorSelectionEnergy M P := by
  unfold mobiusDivisorSelectionEnergy subsetLabelEnergy
  apply sum_congr rfl
  intro R hR
  congr 1
  unfold subsetLabelFibre
  apply sum_congr rfl
  intro d hd
  have hpD : p ∉ d.primeFactors := by
    intro h
    have hpd := Nat.le_of_mem_primeFactors h
    have hdM := mem_Icc.mp (mem_filter.mp hd).1
    omega
  rw [Finset.sdiff_insert_of_notMem hpD]

private lemma prefix_young {p : ℝ} (hp : 0 < p) (a b : ℝ) :
    -2*(a*b) ≤ (2/p)*a^2+(p/2)*b^2 := by
  have h : (-2*(a*b))*p ≤ ((2/p)*a^2+(p/2)*b^2)*p := by
    field_simp
    nlinarith only [sq_nonneg (2*a+p*b)]
  nlinarith only [h,hp]

private lemma prefix_interpolated_budget (M p : ℕ) (hp : 0 < p) (P : Finset ℕ)
    (T : Finset (Finset ℕ)) {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ N : ℕ,mobiusDivisorSelectionEnergy N P ≤ K*(N:ℝ)^2) (hpM : p < M) :
    (∑ R ∈ T,(mobiusDivisorInterpolatedFibre M p P R)^2) ≤ 4*K*(M:ℝ)^2/(p:ℝ)^2 := by
  have hw0 := divisorPrimeClipWeight_nonneg M p hp
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M p := by linarith [divisorPrimeClipWeight_lt_one M p hp]
  have hnext : K*((M/p:ℕ):ℝ)^2 ≤ K*((M/p+1:ℕ):ℝ)^2 := by gcongr; exact Nat.le_succ _
  have hsmall := (hE (M/p)).trans hnext
  have hnext' := hE (M/p+1)
  have hconv := add_le_add (mul_le_mul_of_nonneg_left hsmall hw1)
    (mul_le_mul_of_nonneg_left hnext' hw0)
  have hpack : (∑ R ∈ T,(mobiusDivisorInterpolatedFibre M p P R)^2) ≤ K*((M/p+1:ℕ):ℝ)^2 := by
    have h := (sum_mobiusDivisorInterpolatedFibre_sq_le M p hp P T).trans hconv
    nlinarith only [h]
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hdiv : ((M/p:ℕ):ℝ)*(p:ℝ) ≤ M := by exact_mod_cast Nat.div_mul_le_self M p
  have hpMR : (p:ℝ) ≤ M := by exact_mod_cast hpM.le
  have hN : ((M/p+1:ℕ):ℝ) ≤ 2*(M:ℝ)/(p:ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    push_cast
    nlinarith only [hdiv,hpMR]
  calc
    _ ≤ K*((M/p+1:ℕ):ℝ)^2 := hpack
    _ ≤ K*(2*(M:ℝ)/(p:ℝ))^2 := by gcongr
    _ = _ := by ring

private lemma prefix_insert_budget (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    {K : ℝ} (hK : 0 ≤ K) (hE : ∀ M : ℕ,mobiusDivisorSelectionEnergy M P ≤ K*(M:ℝ)^2) :
    ∀ M : ℕ,mobiusDivisorSelectionEnergy M (insert p P) ≤
      (K*(1+4/Real.sqrt p))*(M:ℝ)^2 := by
  intro M
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hroot : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
  by_cases hpM : p < M
  · let T := ((mobiusDivisorSelectionPrimes M).erase p).powerset
    let a := fun R => mobiusDivisorSelectionFibre M P R
    let b := fun R => mobiusDivisorInterpolatedFibre M p P R
    have ha : (∑ R ∈ T,(a R)^2) ≤ K*(M:ℝ)^2 :=
      (sum_mobiusDivisorSelectionFibre_sq_le_energy M P T).trans (hE M)
    have hb : (∑ R ∈ T,(b R)^2) ≤ 4*K*(M:ℝ)^2/(p:ℝ)^2 :=
      prefix_interpolated_budget M p hp.pos P T hK hE hpM
    have hy : -2*(∑ R ∈ T,a R*b R) ≤
        (2/(p:ℝ))*(∑ R ∈ T,(a R)^2)+((p:ℝ)/2)*(∑ R ∈ T,(b R)^2) := by
      rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib]
      exact sum_le_sum (fun R hR => prefix_young hpR (a R) (b R))
    have hbound := mul_le_mul_of_nonneg_left (hy.trans
      (add_le_add (mul_le_mul_of_nonneg_left ha (by positivity))
        (mul_le_mul_of_nonneg_left hb (by positivity)))) hroot.le
    have hrootdiv : Real.sqrt p/(p:ℝ)=1/Real.sqrt p := by
      apply (div_eq_div_iff hpR.ne' hroot.ne').mpr
      simpa only [one_mul,pow_two] using Real.sq_sqrt hpR.le
    have he : Real.sqrt p*((2/(p:ℝ))*(K*(M:ℝ)^2)+((p:ℝ)/2)*(4*K*(M:ℝ)^2/(p:ℝ)^2)) =
        (4/Real.sqrt p)*(K*(M:ℝ)^2) := by
      calc
        _ = (4*(Real.sqrt p/(p:ℝ)))*(K*(M:ℝ)^2) := by field_simp; ring
        _ = _ := by rw [hrootdiv]; ring
    rw [he] at hbound
    have hrelease := mobiusDivisorSelectionEnergy_insert_interpolation hp M P hpM hpP
    change mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P =
      (-2*Real.sqrt p)*∑ R ∈ T,a R*b R at hrelease
    nlinarith only [hrelease,hbound,hE M]
  · rw [prefix_inactive M p P (le_of_not_gt hpM)]
    have h := mul_nonneg (mul_nonneg hK (show 0 ≤ 4/Real.sqrt p by positivity)) (sq_nonneg (M:ℝ))
    nlinarith only [hE M,h]

private lemma prefix_union_budget (P S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime)
    {K : ℝ} (hK : 0 ≤ K) (hE : ∀ M : ℕ,mobiusDivisorSelectionEnergy M P ≤ K*(M:ℝ)^2) :
    ∀ M : ℕ,mobiusDivisorSelectionEnergy M (P ∪ S) ≤
      (K*∏ p ∈ S,(1+4/Real.sqrt p))*(M:ℝ)^2 := by
  classical
  induction S using Finset.induction with
  | empty => simpa using hE
  | @insert p S hpS ih =>
    have hSpr : ∀ q ∈ S,q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hp := hS p (mem_insert_self p S)
    have hprod : 0 ≤ K*∏ q ∈ S,(1+4/Real.sqrt q) := mul_nonneg hK
      (prod_nonneg (fun q hq => by positivity))
    have hprevious := ih hSpr
    rw [prod_insert hpS,Finset.union_insert]
    by_cases hpP : p ∈ P ∪ S
    · rw [Finset.insert_eq_of_mem hpP]
      intro M
      have hmore : 0 ≤ (K*∏ q ∈ S,(1+4/Real.sqrt q))*(4/Real.sqrt p)*(M:ℝ)^2 := by positivity
      nlinarith only [hprevious M,hmore]
    · intro M
      have h := prefix_insert_budget (P ∪ S) hp hpP hprod hprevious M
      convert h using 1; ring

private lemma prefix_halfweight_budget (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (M : ℕ) :
    mobiusDivisorSelectionEnergy M P ≤
      ((9/25:ℝ)*Real.exp (4*∑ p ∈ P,(Real.sqrt p)⁻¹))*(M:ℝ)^2 := by
  have h := prefix_union_budget ∅ P hP (by norm_num : (0:ℝ) ≤ 9/25)
    mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq M
  rw [Finset.empty_union] at h
  apply h.trans
  have he := Real.prod_one_add_le_exp_sum P (fun p => (show 0 ≤ 4/Real.sqrt p by positivity))
  simp only [div_eq_mul_inv] at he
  rw [← mul_sum] at he
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 9/25)) (sq_nonneg (M:ℝ))

/-- Fresh actual preparation makes any prescribed missing prime release energy
over an arbitrary inherited nonempty core and on a common integer-cutoff tail. -/
theorem exists_mobiusDivisorInheritedPrimeInsertionProducer :
    ∀ P : Finset ℕ,P.Nonempty → (∀ p ∈ P,p.Prime) →
      ∀ r : ℕ,r.Prime → r ∉ P → ∀ B : ℕ,
      ∃ S : Finset ℕ,(∀ p ∈ S,p.Prime ∧ B < p) ∧ Disjoint P S ∧ r ∉ S ∧
        (∑' n,mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n) <
          (∑' n,mobiusDivisorFixedCoreBlockMass (P ∪ S) n) ∧
        ∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,c*(M:ℝ)^2 ≤
          mobiusDivisorSelectionEnergy M (P ∪ S)-mobiusDivisorSelectionEnergy M (insert r (P ∪ S)) := by
  intro P hP hprime r hr hrP B
  obtain ⟨W,hW,h⟩ := prefix_weighted_insertion P hP hprime r hr hrP
  obtain ⟨S,hS,hPS,hrS,hmass,hE,htail⟩ := h B
  exact ⟨S,hS,hPS,hrS,hE,htail⟩

/-- A fixed inherited core and prescribed missing prime admit one preparation
budget valid at every cutoff, for every helper subset, and at arbitrarily large
helper-prime distances. The prescribed insertion strictly releases energy on
a common cutoff tail. The budget is chosen before the prime-distance bound. -/
theorem exists_mobiusDivisorBudgetedInheritedPrimeInsertionProducer :
    ∀ P : Finset ℕ,P.Nonempty → (∀ p ∈ P,p.Prime) →
      ∀ r : ℕ,r.Prime → r ∉ P → ∃ K : ℝ,0 < K ∧ ∀ B : ℕ,
      ∃ S : Finset ℕ,(∀ p ∈ S,p.Prime ∧ B < p) ∧ Disjoint P S ∧ r ∉ S ∧
        (∑' n,mobiusDivisorFixedCoreBlockMass (insert r (P ∪ S)) n) <
          (∑' n,mobiusDivisorFixedCoreBlockMass (P ∪ S) n) ∧
        (∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,c*(M:ℝ)^2 ≤
          mobiusDivisorSelectionEnergy M (P ∪ S)-mobiusDivisorSelectionEnergy M (insert r (P ∪ S))) ∧
        ∀ T : Finset ℕ,T ⊆ S → ∀ M : ℕ,
          mobiusDivisorSelectionEnergy M (P ∪ T) ≤ K*(M:ℝ)^2 ∧
          mobiusDivisorSelectionEnergy M (insert r (P ∪ T)) ≤ K*(M:ℝ)^2 := by
  classical
  intro P hP hprime r hr hrP
  obtain ⟨W,hW,h⟩ := prefix_weighted_insertion P hP hprime r hr hrP
  let A : ℝ := (∑ p ∈ P,(Real.sqrt p)⁻¹)+W+(Real.sqrt r)⁻¹
  let K : ℝ := (9/25)*Real.exp (4*A)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro B
  obtain ⟨S,hS,hPS,hrS,hmass,hE,htail⟩ := h B
  refine ⟨S,hS,hPS,hrS,hE,htail,?_⟩
  intro T hTS M
  have hTprime : ∀ p ∈ T,p.Prime := fun p hp => (hS p (hTS hp)).1
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    exact Finset.disjoint_left.mp hPS hp (hTS hpt)
  have hQT : ∀ p ∈ P ∪ T,p.Prime := by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (hprime p) (hTprime p)
  have hrPT : r ∉ P ∪ T := by
    intro hrt
    exact (Finset.mem_union.mp hrt).elim hrP (fun ht => hrS (hTS ht))
  have hRprime : ∀ p ∈ insert r (P ∪ T),p.Prime := by simpa using And.intro hr hQT
  have hmT : (∑ p ∈ T,(Real.sqrt p)⁻¹) ≤ W :=
    (Finset.sum_le_sum_of_subset_of_nonneg hTS (fun p hp hnot => by positivity)).trans hmass
  have hmQT : (∑ p ∈ P ∪ T,(Real.sqrt p)⁻¹) ≤ A := by
    rw [Finset.sum_union hPT]
    dsimp [A]
    linarith [inv_nonneg.mpr (Real.sqrt_nonneg (r:ℝ))]
  have hmR : (∑ p ∈ insert r (P ∪ T),(Real.sqrt p)⁻¹) ≤ A := by
    rw [Finset.sum_insert hrPT,Finset.sum_union hPT]
    dsimp [A]
    linarith only [hmT]
  constructor
  · apply (prefix_halfweight_budget (P ∪ T) hQT M).trans
    dsimp [K]
    gcongr
  · apply (prefix_halfweight_budget (insert r (P ∪ T)) hRprime M).trans
    dsimp [K]
    gcongr

end RHTower
