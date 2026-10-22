import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticNativeCuspModes
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Source-derived decay of the complete nonconstant native cusp mass

Native weighted admission supplies arbitrarily far comparison endpoints; no
upper-cusp value is prescribed. A finite maximum principle then bounds each
original forced mode by an exponential lower-endpoint term and a power tail
with inverse-square frequency weight. Parseval and integer p-series summability
retain every nonzero mode and give rapid decay for the complete nonconstant
slice mass. The exact full-mass decomposition retains the native zero mode.

Every public estimate is specialised to the constructed original responses,
with both physical branches and their full forcing. The cutoff height changes
neither the spectral parameter nor the common Hawking clock. Derivative-product
control, complete tested-current limits, physical left-QNM identification and
fixed-clock extinction are not asserted here.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower.SelbergMaassFourier
namespace RHTower.D4BMQuarticNativeCuspComparison
open D4BMModularCore D4BMGlobalAngularResponse D4BMQuarticNativeCuspModes
noncomputable section
set_option autoImplicit false

private theorem second_nonpos_at_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp := lt_of_not_ge h
  have hn := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm,hn] with y hy hz
    exact le_antisymm hy hz
  have hzero : deriv (deriv f) x = 0 := by
    simpa using he.deriv.deriv_eq
  linarith

private theorem finite_comparison {v : ℝ → ℝ} {A B L : ℝ} (hAB : A ≤ B)
    (hL : 0 < L) (hc : ContinuousOn v (Icc A B))
    (hA : v A ≤ 0) (hB : v B ≤ 0)
    (hr : ∀ x ∈ Ioo A B, L*v x ≤ deriv (deriv v) x) :
    ∀ x ∈ Icc A B, v x ≤ 0 := by
  obtain ⟨c,hcI,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨A,⟨le_rfl,hAB⟩⟩ hc
  intro x hx
  by_contra h
  have hp : 0 < v c := (lt_of_not_ge h).trans_le (hmax hx)
  have hAc : A < c := lt_of_le_of_ne hcI.1 (by intro he; subst c; linarith)
  have hcB : c < B := lt_of_le_of_ne hcI.2 (by intro he; subst c; linarith)
  have hm := hmax.isLocalMax (Icc_mem_nhds hAc hcB)
  have hn := second_nonpos_at_max hm (hc.continuousAt (Icc_mem_nhds hAc hcB))
  have hd := hr c ⟨hAc,hcB⟩
  have hh := mul_pos hL hp
  linarith

private theorem exists_small_tail {u : ℝ → ℝ} {A e T : ℝ}
    (hA : 0 < A) (he : 0 < e)
    (hu : IntegrableOn (fun y : ℝ => u y/y^2) (Ioi A)) :
    ∃ B : ℝ, max A T ≤ B ∧ u B ≤ e*B := by
  by_contra! h
  let C := max A T
  have hC : 0 < C := hA.trans_le (le_max_left _ _)
  have hi := ((hu.mono_set (Ioi_subset_Ioi (le_max_left A T))).const_mul e⁻¹)
  have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi C) := by
    apply hi.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hCy : C < y := hy
    have hp : 0 < y := hC.trans hCy
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    calc
      y⁻¹ = e⁻¹*((e*y)/y^2) := by field_simp
      _ ≤ e⁻¹*(u y/y^2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (h y hCy.le).le (sq_nonneg y)) (inv_nonneg.mpr he.le)
  exact not_integrableOn_Ioi_inv hinv

private theorem weighted_comparison {u b : ℝ → ℝ} {A L : ℝ}
    (hA : 0 < A) (hL : 0 < L)
    (hu : ∀ y ∈ Ici A, HasDerivAt u (deriv u y) y)
    (hdu : ∀ y ∈ Ici A, HasDerivAt (deriv u) (deriv (deriv u) y) y)
    (hb : ∀ y ∈ Ici A, HasDerivAt b (deriv b y) y)
    (hdb : ∀ y ∈ Ici A, HasDerivAt (deriv b) (deriv (deriv b) y) y)
    (hi : IntegrableOn (fun y : ℝ => u y/y^2) (Ioi A))
    (hbase : u A ≤ b A) (hb0 : ∀ y ∈ Ici A, 0 ≤ b y)
    (hr : ∀ y ∈ Ici A, L*(u y-b y) ≤ deriv (deriv u) y-deriv (deriv b) y) :
    ∀ y ∈ Ici A, u y ≤ b y := by
  intro y hy
  have hyp : 0 < y := hA.trans_le hy
  by_contra h
  have hgap : 0 < u y-b y := sub_pos.mpr (lt_of_not_ge h)
  let e := (u y-b y)/(2*y)
  have he : 0 < e := div_pos hgap (by positivity)
  obtain ⟨B,hB,hsmall⟩ := exists_small_tail (T := y) hA he hi
  have hAB : A ≤ B := (le_max_left _ _).trans hB
  have hyB : y ≤ B := (le_max_right _ _).trans hB
  let v := fun t : ℝ => u t-b t-e*t
  have hv (t : ℝ) (ht : t ∈ Ici A) :
      HasDerivAt v (deriv u t-deriv b t-e) t := by
    simpa only [v,Pi.sub_apply,id_eq,mul_one] using!
      ((hu t ht).sub (hb t ht)).sub ((hasDerivAt_id t).const_mul e)
  have hvv (t : ℝ) (ht : A < t) :
      deriv (deriv v) t = deriv (deriv u) t-deriv (deriv b) t := by
    have hd : deriv v =ᶠ[𝓝 t] (fun z => deriv u z-deriv b z-e) := by
      filter_upwards [Ioi_mem_nhds ht] with z hz
      exact (hv z (show A ≤ z from (show A < z from hz).le)).deriv
    rw [hd.deriv_eq]
    exact (((hdu t ht.le).sub (hdb t ht.le)).sub_const e).deriv
  have hc : ContinuousOn v (Icc A B) := fun t ht => (hv t ht.1).continuousAt.continuousWithinAt
  have hvA : v A ≤ 0 := by
    dsimp only [v]
    nlinarith [mul_nonneg he.le hA.le]
  have hvB : v B ≤ 0 := by
    dsimp only [v]
    linarith [hb0 B hAB]
  have hvreact (t : ℝ) (ht : t ∈ Ioo A B) : L*v t ≤ deriv (deriv v) t := by
    rw [hvv t ht.1]
    have hp : 0 < t := hA.trans ht.1
    have hh := hr t ht.1.le
    dsimp only [v]
    nlinarith [mul_nonneg (mul_nonneg hL.le he.le) hp.le]
  have hbound := finite_comparison hAB hL hc hvA hvB hvreact y ⟨hy,hyB⟩
  have heq : e*y=(u y-b y)/2 := by dsimp only [e]; field_simp
  dsimp only [v] at hbound
  rw [heq] at hbound
  linarith

private theorem frequency_sq_ge_two (n : {n : ℤ // n ≠ 0}) :
    2 ≤ (signedFrequency 1 n.val)^2 := by
  have hnZ : (1:ℤ) ≤ n.val^2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero n.2)
  have hnR : (1:ℝ) ≤ (n.val:ℝ)^2 := by exact_mod_cast hnZ
  have hm := mul_le_mul_of_nonneg_left hnR (sq_nonneg (2*Real.pi))
  dsimp only [signedFrequency]
  rw [div_one,mul_pow]
  nlinarith [Real.pi_gt_three,sq_nonneg (Real.pi-3)]

private theorem forcing_power_bound (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ y : Ioi (3:ℝ),
      Complex.normSq (forcingMode q b n y)/y.val^4 ≤ C*y.val^(-((2*N+4:ℕ):ℝ)) := by
  obtain ⟨A,hA,hb⟩ := forcingMode_weighted_bound q b (N:ℂ)
  refine ⟨A^2,sq_nonneg A,?_⟩
  intro n y
  have hy : 0 < y.val := lt_trans (by norm_num : (0:ℝ)<3) y.2
  have ha := hb n y
  rw [Complex.cpow_natCast,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy] at ha
  have hs : (y.val^N*‖forcingMode q b n y‖)^2 ≤ A^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr ha)
      (add_nonneg hA (mul_nonneg (pow_nonneg hy.le N) (norm_nonneg (forcingMode q b n y))))
    nlinarith
  have hpower : y.val^(2*N+4)=(y.val^N)^2*y.val^4 := by
    rw [pow_add,show 2*N=N*2 by omega,pow_mul]
  have hsq : Complex.normSq (forcingMode q b n y) ≤ A^2/(y.val^N)^2 := by
    rw [le_div_iff₀ (sq_pos_of_pos (pow_pos hy N)),Complex.normSq_eq_norm_sq]
    nlinarith [hs]
  calc
    _ ≤ (A^2/(y.val^N)^2)/y.val^4 := div_le_div_of_nonneg_right hsq (pow_nonneg hy.le 4)
    _ = _ := by rw [Real.rpow_neg hy.le,Real.rpow_natCast,hpower]; ring

private def barrier (D C L p Y y : ℝ) : ℝ :=
  D*Real.exp (Y-y)+(2*C/L)*y^(-p)

private theorem barrier_hasDerivAt (D C L p Y : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (barrier D C L p Y)
      (-D*Real.exp (Y-y)+(2*C/L)*(-p)*y^(-p-1)) y := by
  have h := (((hasDerivAt_id y).const_sub Y).exp.const_mul D).add
    ((Real.hasDerivAt_rpow_const (p := -p) (Or.inl hy.ne')).const_mul (2*C/L))
  simp only [id_eq] at h
  convert h using 1 <;> try rfl
  ring

private theorem barrier_second_hasDerivAt (D C L p Y : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (barrier D C L p Y))
      (D*Real.exp (Y-y)+(2*C/L)*p*(p+1)*y^(-p-2)) y := by
  have h := (((hasDerivAt_id y).const_sub Y).exp.const_mul (-D)).add
    ((Real.hasDerivAt_rpow_const (p := -p-1) (Or.inl hy.ne')).const_mul ((2*C/L)*(-p)))
  have he : deriv (barrier D C L p Y) =ᶠ[𝓝 y]
      (fun t => -D*Real.exp (Y-t)+(2*C/L)*(-p)*t^(-p-1)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (barrier_hasDerivAt D C L p Y ht).deriv
  simp only [id_eq] at h
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [show -p-1-1=-p-2 by ring]
  ring

private theorem barrier_reaction {D C L p Y y : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hL : 2 ≤ L) (hp : 0 ≤ p)
    (hy : 0 < y) (hpy : p+1 ≤ y) :
    deriv (deriv (barrier D C L p Y)) y ≤
      L*barrier D C L p Y y-C*y^(-p) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hcoef : p*(p+1)/y^2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos hy)]
    nlinarith [sq_nonneg (y-(p+1))]
  have hCcoef : (2*C/L)*(p*(p+1)/y^2) ≤ C := by
    calc
      _ ≤ (2*C/L)*1 := mul_le_mul_of_nonneg_left hcoef (div_nonneg (by positivity) hLp.le)
      _ ≤ C := by rw [mul_one,div_le_iff₀ hLp]; nlinarith
  rw [(barrier_second_hasDerivAt D C L p Y hy).deriv,barrier,
    Real.rpow_sub hy (-p) 2,Real.rpow_two]
  have hpow : 0 ≤ y^(-p) := Real.rpow_nonneg hy.le _
  have hdexp : 0 ≤ D*Real.exp (Y-y) := mul_nonneg hD (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hCcoef hpow
  have he : (2*C/L)*p*(p+1)*(y^(-p)/y^2) =
      ((2*C/L)*(p*(p+1)/y^2))*y^(-p) := by ring
  rw [he]
  have he2 : L*((2*C/L)*y^(-p))=2*C*y^(-p) := by field_simp
  have he3 : L*(D*Real.exp (Y-y)+(2*C/L)*y^(-p)) =
      L*(D*Real.exp (Y-y))+2*C*y^(-p) := by rw [mul_add,he2]
  rw [he3]
  nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ L by linarith)) hdexp]

/-- Every original nonzero native mode is bounded by a decaying lower-endpoint term
and a source-derived inverse-square-frequency tail. No upper boundary value is supplied. -/
theorem nativeMode_cusp_bound (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ Y : ℝ, 4 ≤ Y ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : {n : ℤ // n ≠ 0}, ∀ y : Ici Y,
        modeMass q b n.val y ≤ modeMass q b n.val Y*Real.exp (Y-y.val)+
          C/(signedFrequency 1 n.val)^2*y.val^(-((2*N+4:ℕ):ℝ)) := by
  obtain ⟨C,hC,hF⟩ := forcing_power_bound q b N
  let p : ℝ := (2*N+4:ℕ)
  let Y := max 4 (max (coercivityHeight q b) (p+1))
  have hY4 : 4 ≤ Y := le_max_left _ _
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY4
  have hYc : coercivityHeight q b ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYp : p+1 ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Y,hY4,2*C,by positivity,?_⟩
  intro n y
  let L := (signedFrequency 1 n.val)^2
  let u := modeMass q b n.val
  let B := barrier (u Y) C L p Y
  have hL : 2 ≤ L := frequency_sq_ge_two n
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hpos (t : ℝ) (ht : t ∈ Ici Y) : 0 < t := hYpos.trans_le ht
  have hu (t : ℝ) (ht : t ∈ Ici Y) : HasDerivAt u (deriv u t) t :=
    (modeMass_hasDerivAt q b n.val ⟨t,hpos t ht⟩).differentiableAt.hasDerivAt
  have hdu (t : ℝ) (ht : t ∈ Ici Y) : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (modeMass_second_hasDerivAt q b n.val ⟨t,hpos t ht⟩).differentiableAt.hasDerivAt
  have hb (t : ℝ) (ht : t ∈ Ici Y) : HasDerivAt B (deriv B t) t :=
    (barrier_hasDerivAt (u Y) C L p Y (hpos t ht)).differentiableAt.hasDerivAt
  have hdb (t : ℝ) (ht : t ∈ Ici Y) : HasDerivAt (deriv B) (deriv (deriv B) t) t :=
    (barrier_second_hasDerivAt (u Y) C L p Y (hpos t ht)).differentiableAt.hasDerivAt
  have hi : IntegrableOn (fun t : ℝ => u t/t^2) (Ioi Y) :=
    (modeMass_density_integrable q b n.val).mono_set (Ioi_subset_Ioi (by linarith))
  have hbase : u Y ≤ B Y := by
    dsimp only [B,barrier]
    rw [sub_self,Real.exp_zero,mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (by positivity) hLp.le)
      (Real.rpow_nonneg hYpos.le _))
  have hb0 (t : ℝ) (ht : t ∈ Ici Y) : 0 ≤ B t := by
    dsimp only [B,barrier]
    exact add_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg (div_nonneg (by positivity) hLp.le) (Real.rpow_nonneg (hpos t ht).le _))
  have hr (t : ℝ) (ht : t ∈ Ici Y) :
      L*(u t-B t) ≤ deriv (deriv u) t-deriv (deriv B) t := by
    have hc := modeMass_cusp_coercivity q b n ⟨t,hYc.trans ht⟩
    have hf := hF n.val ⟨t,lt_of_lt_of_le (by linarith : 3 < Y) ht⟩
    have hbar := barrier_reaction (D := u Y) (C := C) (L := L) (p := p) (Y := Y)
      (Complex.normSq_nonneg _) hC hL (by positivity) (hpos t ht) (hYp.trans ht)
    change 2*Complex.normSq (deriv (responseMode q b n.val) t)+L*u t-
      Complex.normSq (forcingMode q b n.val t)/t^4 ≤ deriv (deriv u) t at hc
    change Complex.normSq (forcingMode q b n.val t)/t^4 ≤ C*t^(-p) at hf
    change deriv (deriv B) t ≤ L*B t-C*t^(-p) at hbar
    nlinarith [Complex.normSq_nonneg (deriv (responseMode q b n.val) t)]
  exact weighted_comparison hYpos hLp hu hdu hb hdb hi hbase hb0 hr y.val y.2

/-- The complete nonconstant native slice mass, retaining every nonzero Fourier mode. -/
def nonconstantMass (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℝ :=
  ∑' n : {n : ℤ // n ≠ 0}, modeMass q b n.val y

/-- The complete native slice retains its original zero mode alongside the full
nonconstant mass. No homogeneous coefficient is discarded. -/
theorem nativeMass_decomposition (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    D4BMCuspResponse.responseMeanSquare q b y =
      modeMass q b 0 y+nonconstantMass q b y := by
  have hs := modeMass_hasSum q b y
  have he := hs.summable.sum_add_tsum_subtype_compl ({0} : Finset ℤ)
  have htail : (∑' n : {n : ℤ // n ∉ ({0} : Finset ℤ)}, modeMass q b n.val y) =
      nonconstantMass q b y := by
    unfold nonconstantMass
    exact tsum_congr_subtype (fun n : ℤ => modeMass q b n y)
      (fun _ => not_congr Finset.mem_singleton)
  rw [Finset.sum_singleton,hs.tsum_eq] at he
  exact he.symm.trans (congrArg (fun t : ℝ => modeMass q b 0 y+t) htail)

private theorem frequency_summable :
    Summable (fun n : {n : ℤ // n ≠ 0} => 1/(signedFrequency 1 n.val)^2) := by
  have hs := ((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)).mul_left
    (1/(2*Real.pi)^2)
  apply (hs.subtype (fun n : ℤ => n ≠ 0)).congr
  intro n
  change (1/(2*Real.pi)^2)*(1/(n.val:ℝ)^2) = 1/(signedFrequency 1 n.val)^2
  simp only [signedFrequency,mul_pow,div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- Summation preserves the source-derived cusp comparison across all nonconstant modes. -/
theorem nonconstantMass_cusp_bound (q : XiZeroCopy) (b : Bool) (N : ℕ) :
    ∃ Y : ℝ, 4 ≤ Y ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Ici Y,
      nonconstantMass q b y ≤ nonconstantMass q b Y*Real.exp (Y-y.val)+
        C*y.val^(-((2*N+4:ℕ):ℝ)) := by
  obtain ⟨Y,hY,C,hC,hb⟩ := nativeMode_cusp_bound q b N
  let S : ℝ := ∑' n : {n : ℤ // n ≠ 0}, 1/(signedFrequency 1 n.val)^2
  have hS : 0 ≤ S := tsum_nonneg (fun _ => div_nonneg (by norm_num) (sq_nonneg _))
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hsY := (modeMass_hasSum q b ⟨Y,hYpos⟩).summable.subtype (fun n : ℤ => n ≠ 0)
  change Summable (fun n : {n : ℤ // n ≠ 0} => modeMass q b n.val Y) at hsY
  refine ⟨Y,hY,C*S,mul_nonneg hC hS,?_⟩
  intro y
  have hypos : 0 < y.val := hYpos.trans_le y.2
  have hsy := (modeMass_hasSum q b ⟨y.val,hypos⟩).summable.subtype (fun n : ℤ => n ≠ 0)
  change Summable (fun n : {n : ℤ // n ≠ 0} => modeMass q b n.val y.val) at hsy
  have hA := hsY.mul_right (Real.exp (Y-y.val))
  have hB := (frequency_summable.mul_left C).mul_right (y.val^(-((2*N+4:ℕ):ℝ)))
  have hterm (n : {n : ℤ // n ≠ 0}) : modeMass q b n.val y ≤
      modeMass q b n.val Y*Real.exp (Y-y.val)+
        (C*(1/(signedFrequency 1 n.val)^2))*y.val^(-((2*N+4:ℕ):ℝ)) := by
    simpa only [div_eq_mul_inv,one_mul] using hb n y
  have ht := hsy.tsum_le_tsum hterm (hA.add hB)
  rw [hA.tsum_add hB,tsum_mul_right,tsum_mul_right,tsum_mul_left] at ht
  exact ht

/-- Native admission and the complete forcing imply rapid decay of the entire
nonconstant cusp mass, without an assumed upper boundary value. -/
theorem nonconstantMass_weighted_tendsto_zero (q : XiZeroCopy) (b : Bool) (r : ℝ) :
    Tendsto (fun y : ℝ => y^r*nonconstantMass q b y) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt r
  obtain ⟨Y,hY,C,hC,hbound⟩ := nonconstantMass_cusp_bound q b N
  let p : ℝ := (2*N+4:ℕ)
  have hpr : 0 < p-r := by
    dsimp only [p]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have ht1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r 1 (by norm_num)).const_mul
    (nonconstantMass q b Y*Real.exp Y)
  have ht2 := (tendsto_rpow_neg_atTop hpr).const_mul C
  have ht := ht1.add ht2
  apply squeeze_zero_norm' ?_ (by simpa only [mul_zero,add_zero] using ht)
  filter_upwards [eventually_ge_atTop Y] with y hy
  have hpos : 0 < y := lt_of_lt_of_le (by linarith : 0 < Y) hy
  have hm : 0 ≤ nonconstantMass q b y := tsum_nonneg (fun _ => Complex.normSq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hpos.le _) hm)]
  have h := mul_le_mul_of_nonneg_left (hbound ⟨y,hy⟩) (Real.rpow_nonneg hpos.le r)
  have he : Real.exp (Y-y)=Real.exp Y*Real.exp (-y) := by rw [sub_eq_add_neg,Real.exp_add]
  have hp : y^r*y^(-p)=y^(-(p-r)) := by rw [← Real.rpow_add hpos]; congr 1; ring
  calc
    _ ≤ y^r*(nonconstantMass q b Y*Real.exp (Y-y)+C*y^(-p)) := h
    _ = (nonconstantMass q b Y*Real.exp Y)*(y^r*Real.exp (-(1:ℝ)*y))+C*y^(-(p-r)) := by
      rw [he,mul_add]
      calc
        _ = (nonconstantMass q b Y*Real.exp Y)*(y^r*Real.exp (-y))+C*(y^r*y^(-p)) := by ring
        _ = _ := by rw [hp]; simp only [neg_mul,one_mul]

/-- The full native slice mass approaches its retained zero-mode mass with every
real polynomial weight. -/
theorem nativeMass_remainder_weighted_tendsto_zero (q : XiZeroCopy) (b : Bool) (r : ℝ) :
    Tendsto (fun y : ℝ => y^r*(D4BMCuspResponse.responseMeanSquare q b y-
      modeMass q b 0 y)) atTop (𝓝 0) := by
  apply (nonconstantMass_weighted_tendsto_zero q b r).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [nativeMass_decomposition q b ⟨y,hy⟩,add_sub_cancel_left]

end
end RHTower.D4BMQuarticNativeCuspComparison
