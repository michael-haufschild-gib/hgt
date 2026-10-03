import GaloisForLFunctions.RHTower.ChiPrimeGaussianRationalProfile

/-!
# Complete physical cubic rows near fixed rational frequencies

The actual moving height window is retained. Exact rational phase partition controls
the full prime q-row, and both stationary-kernel remainders and the removed exact
contraction are paid explicitly. This is not a bound for the full joint p,r average.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Residual physical frequency from the rational reference A/Q. -/
def primeGaussianCubicRationalFrequency (A Q : ℕ) (N : ℝ) (p r : ℕ) : ℝ :=
  2*Real.pi*N*((p:ℝ)/r-(A:ℝ)/Q)

private def rationalRowFactor (N : ℝ) (p r : ℕ) : ℂ :=
  (2*Real.pi:ℂ)*smoothAFECutoff ((p:ℝ)/N)*(starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)

private theorem rational_row_phase (A Q : ℕ) [NeZero Q] {N : ℝ} (hN : N≠0)
    (p q : ℕ) {r : ℕ} (hr : (r:ℝ)≠0) :
    bourgainOscillation (2*Real.pi*((p:ℝ)*q/r)) =
      primeRationalPhase A Q q*
        bourgainOscillation (primeGaussianCubicRationalFrequency A Q N p r*((q:ℝ)/N)) := by
  have hQ : (Q:ℝ)≠0 := by exact_mod_cast NeZero.ne Q
  have he : 2*Real.pi*((p:ℝ)*q/r) =
      2*Real.pi*((A:ℝ)/Q)*q+primeGaussianCubicRationalFrequency A Q N p r*((q:ℝ)/N) := by
    dsimp only [primeGaussianCubicRationalFrequency]
    field_simp; ring
  rw [he]
  unfold primeRationalPhase bourgainOscillation
  rw [Complex.ofReal_add,mul_add,Complex.exp_add]

private theorem rational_row_main_entry (A Q : ℕ) [NeZero Q] {N : ℝ} (hN : N≠0)
    (p q : ℕ) {r : ℕ} (hr : (r:ℝ)≠0) :
    primeGaussianCubicMainEntry N p q r = rationalRowFactor N p r*
      (primeGaussianScaledProfile ((p:ℝ)/r) ((q:ℝ)/N)*
        bourgainOscillation (primeGaussianCubicRationalFrequency A Q N p r*((q:ℝ)/N)))*
          primeRationalPhase A Q q := by
  rw [primeGaussianCubicMainEntry,rational_row_phase A Q hN p q hr]
  have he : (p:ℝ)*q/((r:ℝ)*N) = ((p:ℝ)/r)*((q:ℝ)/N) := by
    field_simp
  rw [he]
  dsimp only [rationalRowFactor,primeGaussianScaledProfile]
  ring

private theorem rational_row_factor_norm {N : ℝ} (hN : 0<N) {p r : ℕ}
    (hp : p∈primeProfileBand N) (hr : r∈primeProfileBand N) :
    ‖rationalRowFactor N p r‖≤8/N := by
  obtain ⟨_,hpN,_⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_,hrN,_⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hpn := norm_smoothAFECutoff_le_one (div_pos (hN.trans hpN) hN)
  have hrn := norm_smoothAFECutoff_le_one (div_pos hr0 hN)
  dsimp [rationalRowFactor]
  rw [norm_div,norm_mul,norm_mul,Complex.norm_conj,
    show (2*↑Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by positivity : 0≤2*Real.pi),Complex.norm_natCast]
  calc
    _ ≤ (2*Real.pi)*1*1/r := by gcongr
    _ ≤ 8/N := by
      apply (div_le_div_iff₀ hr0 hN).mpr
      nlinarith [Real.pi_lt_four]

private theorem rational_row_main_norm {N : ℝ} (hN : 0<N) {p q r : ℕ}
    (hp : p∈primeProfileBand N) (hq : q∈primeProfileBand N) (hr : r∈primeProfileBand N) :
    ‖primeGaussianCubicMainEntry N p q r‖≤8/N := by
  have hr0 : (0:ℝ)<r := hN.trans (primeProfileBand_mem hN.le hr).2.1
  rw [rational_row_main_entry 0 1 hN.ne' p q hr0.ne']
  have hqn := norm_smoothAFECutoff_le_one (div_pos (hN.trans (primeProfileBand_mem hN.le hq).2.1) hN)
  have hprofile : ‖primeGaussianScaledProfile ((p:ℝ)/r) ((q:ℝ)/N)‖≤1 := by
    rw [primeGaussianScaledProfile,norm_mul,Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact (mul_le_mul bagPhysicalHeightWindow.le_one hqn (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  simp only [norm_mul,primeRationalPhase,norm_bourgainOscillation,mul_one]
  exact (mul_le_mul (rational_row_factor_norm hN hp hr) hprofile (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

private theorem exists_rational_row_signed_physical_error (Q : ℕ) [NeZero Q] :
    ∃ K:ℝ, 0<K ∧ ∀ A:ℕ, ∀ N:ℝ, 1<N → ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r-
        (rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
          (primeGaussianCubicRationalFrequency A Q N p r)-primeGaussianCubicMainEntry N p r r)‖≤
        K/(N*Real.log N) := by
  obtain ⟨Cp,hCp,hphysical⟩ := exists_primeGaussianCubic_entry_error
  let H : ℝ := 2*Real.log 4
  have hH : 0<H := by dsimp [H];positivity
  refine ⟨Cp*H,by positivity,?_⟩
  intro A N hN p hp r hr
  have hN0 : 0<N := by linarith only [hN]
  have hlog : 0<Real.log N := Real.log_pos hN
  have hr0 : (0:ℝ)<r := hN0.trans (primeProfileBand_mem hN0.le hr).2.1
  let V : ℕ→ℂ := fun q => primeGaussianCubicCoefficient N p q r*primeGaussianCubicKernel N p q r
  let F : ℕ→ℂ := fun q => primeGaussianCubicMainEntry N p q r
  let D : ℕ→ℂ := fun q => if q=r then 0 else V q-F q
  have hE : 0≤Cp/N^2 := by positivity
  have hd (q:ℕ) (hq:q∈primeProfileBand N) : ‖D q‖≤Cp/N^2 := by
    dsimp only [D]
    split_ifs with heq
    · simpa only [norm_zero] using hE
    · exact hphysical N hN p hp q hq r hr
  have hident : primeGaussianCubicCompleteRow N p r =
      (∑ q∈primeProfileBand N,D q)+(∑ q∈primeProfileBand N,F q)-F r := by
    have hpoint (q:ℕ) : (if q=r then 0 else V q)=D q+F q-(if q=r then F r else 0) := by
      dsimp [D]
      split_ifs with h <;> simp [h]
    change (∑ q∈primeProfileBand N,if q=r then 0 else V q)=_
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq']
    simp only [hr,ite_true]
  have hD : ‖∑ q∈primeProfileBand N,D q‖≤(primeProfileBand N).card*(Cp/N^2) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum hd).trans_eq (by simp))
  have hcount : (primeProfileBand N).card*(Cp/N^2)≤Cp*H/(N*Real.log N) := by
    have hc := primeProfileBand_card_log_le hN
    change (primeProfileBand N).card*Real.log N≤H*N at hc
    apply (le_div_iff₀ (mul_pos hN0 hlog)).mpr
    field_simp [hN0.ne']
    nlinarith only [hc]
  have hsum : (∑ q∈primeProfileBand N,F q) = rationalRowFactor N p r*
      primeGaussianRationalProfile A Q ((p:ℝ)/r) N (primeGaussianCubicRationalFrequency A Q N p r) := by
    simp only [F,primeGaussianRationalProfile,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact (rational_row_main_entry A Q hN0.ne' p q hr0.ne').trans (by ring)
  rw [hident,hsum]
  have heq : (∑ q∈primeProfileBand N,D q)+
      rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
        (primeGaussianCubicRationalFrequency A Q N p r)-F r-
      (rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
        (primeGaussianCubicRationalFrequency A Q N p r)-primeGaussianCubicMainEntry N p r r) =
        ∑ q∈primeProfileBand N,D q := by dsimp only [F];ring
  rw [heq]
  exact hD.trans hcount

private theorem exists_rational_row_physical_error (Q : ℕ) [NeZero Q] :
    ∃ K:ℝ, 0<K ∧ ∀ A:ℕ, ∀ N:ℝ, 1<N → ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        (8/N)*‖primeGaussianRationalProfile A Q ((p:ℝ)/r) N
          (primeGaussianCubicRationalFrequency A Q N p r)‖+K/(N*Real.log N)+8/N := by
  obtain ⟨K,hK,he⟩ := exists_rational_row_signed_physical_error Q
  refine ⟨K,hK,?_⟩
  intro A N hN p hp r hr
  have hN0 : 0<N := by linarith only [hN]
  have hb := he A N hN p hp r hr
  have hf : ‖rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
      (primeGaussianCubicRationalFrequency A Q N p r)‖≤
      (8/N)*‖primeGaussianRationalProfile A Q ((p:ℝ)/r) N
      (primeGaussianCubicRationalFrequency A Q N p r)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (rational_row_factor_norm hN0 hp hr) (norm_nonneg _)
  have hm := (norm_sub_le
    (rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
      (primeGaussianCubicRationalFrequency A Q N p r)) (primeGaussianCubicMainEntry N p r r)).trans
    (add_le_add hf
      (rational_row_main_norm hN0 hp hr hr))
  have ht := norm_le_norm_sub_add (primeGaussianCubicCompleteRow N p r)
    (rationalRowFactor N p r*primeGaussianRationalProfile A Q ((p:ℝ)/r) N
      (primeGaussianCubicRationalFrequency A Q N p r)-primeGaussianCubicMainEntry N p r r)
  linarith only [ht,hb,hm]

/-- Every complete physical cubic q-row has the constructed rational-neighborhood
estimate. The moving window, both physical kernel remainders and the removed
contraction are retained; there is no amplitude-freezing error. -/
theorem exists_primeGaussianCubicCompleteRow_rational_bound (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ A:ℕ, ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
        primeGaussianCubicRationalFrequency A Q N p r≠0 →
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        C/Real.log N*(1/|primeGaussianCubicRationalFrequency A Q N p r|+
          (1+|primeGaussianCubicRationalFrequency A Q N p r|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))))+
        C/(N*Real.log N)+8/N := by
  obtain ⟨c,B,X,hc,hB,hX,hprofile⟩ := exists_primeGaussianRationalProfile_fourier_bound Q
  obtain ⟨K,hK,hphysical⟩ := exists_rational_row_physical_error Q
  let C := 8*B+K
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨c,C,X,hc,hC,hX,?_⟩
  intro N hN A p hp r hr hτ
  have hN3 := hX.trans hN
  have hN1 : 1<N := by linarith only [hN3]
  have hN0 : 0<N := by linarith only [hN3]
  have hL : 0<Real.log N := Real.log_pos hN1
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem hN0.le hp
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN0.le hr
  have hr0 : (0:ℝ)<r := hN0.trans hrN
  have hξ : (p:ℝ)/r∈Icc (1/2:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hr0).mpr
      linarith only [hpN,hr2]
    · apply (div_le_iff₀ hr0).mpr
      linarith only [hp2,hrN]
  let τ := primeGaussianCubicRationalFrequency A Q N p r
  let E := 1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))
  have hE : 0≤E := by dsimp [E];positivity
  have hmain := hprofile N hN A ((p:ℝ)/r) hξ τ hτ
  have hphys := hphysical A N hN1 p hp r hr
  change ‖primeGaussianRationalProfile A Q ((p:ℝ)/r) N τ‖≤B*N/Real.log N*E at hmain
  change ‖primeGaussianCubicCompleteRow N p r‖≤C/Real.log N*E+C/(N*Real.log N)+8/N
  calc
    _ ≤ (8/N)*‖primeGaussianRationalProfile A Q ((p:ℝ)/r) N τ‖+K/(N*Real.log N)+8/N := hphys
    _ ≤ (8/N)*(B*N/Real.log N*E)+K/(N*Real.log N)+8/N := by gcongr
    _ = (8*B)/Real.log N*E+K/(N*Real.log N)+8/N := by field_simp
    _ ≤ _ := by
      gcongr <;> dsimp [C] <;> linarith only [hB,hK]

/-- Full signed rational main for the contraction-removed physical row. Both the
moving height window and the exact removed diagonal entry are retained. -/
def primeGaussianCubicRationalRowMain (A Q : ℕ) [NeZero Q] (N : ℝ) (p r : ℕ) : ℂ :=
  rationalRowFactor N p r*((N:ℂ)/(Real.log N:ℂ))*(primeGaussianRationalProfileMean A Q*
    (∫ x in (1:ℝ)..2, primeGaussianScaledLogProfile ((p:ℝ)/r) (1/Real.log N) x*
      bourgainOscillation (primeGaussianCubicRationalFrequency A Q N p r*x)))-
        primeGaussianCubicMainEntry N p r r

/-- The actual signed physical q-row has a source-constructed rational main with
its exact contraction removed. This holds at zero residual frequency as well;
no sign or cancellation hypothesis is placed on the remaining p,r sum. -/
theorem exists_primeGaussianCubicCompleteRow_rational_main (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ A:ℕ, ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r-primeGaussianCubicRationalRowMain A Q N p r‖ ≤
        C/Real.log N*(1+|primeGaussianCubicRationalFrequency A Q N p r|)*
          Real.exp (-(c*Real.log N^((1:ℝ)/10)))+C/(N*Real.log N) := by
  obtain ⟨c,B,X,hc,hB,hX,hprofile⟩ := exists_primeGaussianRationalProfile_power_log Q
  obtain ⟨K,hK,hphysical⟩ := exists_rational_row_signed_physical_error Q
  let C := 8*B+K
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨c,C,X,hc,hC,hX,?_⟩
  intro N hN A p hp r hr
  have hN3 := hX.trans hN
  have hN1 : 1<N := by linarith only [hN3]
  have hN0 : 0<N := by linarith only [hN3]
  have hL : 0<Real.log N := Real.log_pos hN1
  have hNC : (N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN0.ne'
  have hLC : (Real.log N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem hN0.le hp
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN0.le hr
  have hr0 : (0:ℝ)<r := hN0.trans hrN
  have hξ : (p:ℝ)/r∈Icc (1/2:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hr0).mpr
      linarith only [hpN,hr2]
    · apply (div_le_iff₀ hr0).mpr
      linarith only [hp2,hrN]
  let τ := primeGaussianCubicRationalFrequency A Q N p r
  let E := (1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))
  let Z := primeGaussianRationalProfile A Q ((p:ℝ)/r) N τ
  let J := primeGaussianRationalProfileMean A Q*(∫ x in (1:ℝ)..2,
    primeGaussianScaledLogProfile ((p:ℝ)/r) (1/Real.log N) x*bourgainOscillation (τ*x))
  let H := rationalRowFactor N p r*Z-primeGaussianCubicMainEntry N p r r
  have hE : 0≤E := by dsimp [E];positivity
  have hb : ‖(Real.log N:ℂ)*Z/(N:ℂ)-J‖≤B*E := by
    exact (hprofile N hN A ((p:ℝ)/r) hξ τ).trans_eq (by dsimp [E];ring)
  have hid : H-primeGaussianCubicRationalRowMain A Q N p r =
      rationalRowFactor N p r*((N:ℂ)/(Real.log N:ℂ))*((Real.log N:ℂ)*Z/(N:ℂ)-J) := by
    dsimp only [H,primeGaussianCubicRationalRowMain,J,τ]
    field_simp
    ring
  have hnorm : ‖H-primeGaussianCubicRationalRowMain A Q N p r‖≤(8*B)/Real.log N*E := by
    rw [hid,norm_mul,norm_mul,norm_div,Complex.norm_of_nonneg hN0.le,Complex.norm_of_nonneg hL.le]
    calc
      _ ≤ ((8/N)*(N/Real.log N))*(B*E) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (rational_row_factor_norm hN0 hp hr) (by positivity))
          hb (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hk : ‖primeGaussianCubicCompleteRow N p r-H‖≤K/(N*Real.log N) :=
    hphysical A N hN1 p hp r hr
  have htotal := (norm_sub_le_norm_sub_add_norm_sub (primeGaussianCubicCompleteRow N p r)
    H (primeGaussianCubicRationalRowMain A Q N p r)).trans (add_le_add hk hnorm)
  have h8 : 8*B≤C := by dsimp [C];linarith only [hK]
  have hKc : K≤C := by dsimp [C];linarith only [hB]
  have he := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h8 hL.le) hE
  have hk' := div_le_div_of_nonneg_right hKc (mul_nonneg hN0.le hL.le)
  refine htotal.trans ?_
  have hh := add_le_add hk' he
  exact hh.trans_eq (by dsimp only [E,τ];ring)

end RHTower
