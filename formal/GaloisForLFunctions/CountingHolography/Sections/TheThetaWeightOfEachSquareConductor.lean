import GaloisForLFunctions.CountingHolography.Sections.TheSignedDegreeAtTheNearestUpperSquare
import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld

/-!
# The theta weight assigned to each square conductor

Adjacent logarithmic cells are assigned to the upper integer root.
After cubic normalization every cell has bounded weight, and every
conductor in the central dyadic band receives a fixed positive weight.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Set _root_.RHTower

/-- Cell of conductor i+2 at square-root scale N. -/
def conductorThetaCell (N i : ℕ) : Set ℝ :=
  Ioc (2*Real.log ((i:ℝ)+1)-2*Real.log N) (2*Real.log ((i:ℝ)+2)-2*Real.log N)

def conductorThetaMass (N i : ℕ) : ℝ := ∫ x in conductorThetaCell N i, thetaCuspFullSource x

/-- Exponent before integer rounding in the product at scale N. -/
def conductorThetaWeight (A : ℝ) (N i : ℕ) : ℝ :=
  A*(N:ℝ)^3*conductorThetaMass N i/((i:ℝ)+2)^2

private abbrev lo (N i : ℕ) := 2*Real.log ((i:ℝ)+1)-2*Real.log N
private abbrev hi (N i : ℕ) := 2*Real.log ((i:ℝ)+2)-2*Real.log N

private theorem phi_integrable : Integrable thetaCuspFullSource := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0

theorem conductorThetaMass_nonneg (N i : ℕ) : 0 ≤ conductorThetaMass N i :=
  integral_nonneg (fun x => (thetaCuspFullSource_pos x).le)

/-- The cell has length between 2/n and 4/n at conductor n=i+2. -/
private theorem cell_length (N i : ℕ) :
    2/((i:ℝ)+2) ≤ hi N i-lo N i ∧ hi N i-lo N i ≤ 4/((i:ℝ)+2) := by
  let x := (i:ℝ)+1
  have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg i)
  have hx₀ := zero_lt_one.trans_le hx
  have hx₁ : 0 < x+1 := by linarith only [hx]
  have hu := Real.log_le_sub_one_of_pos (div_pos hx₁ hx₀)
  have hl := Real.log_le_sub_one_of_pos (div_pos hx₀ hx₁)
  rw [Real.log_div hx₁.ne' hx₀.ne',show (x+1)/x-1=1/x by field_simp] at hu
  rw [Real.log_div hx₀.ne' hx₁.ne',show x/(x+1)-1= -(1/(x+1)) by field_simp; ring] at hl
  have hfrac : 2/x ≤ 4/(x+1) := (div_le_div_iff₀ hx₀ hx₁).mpr (by linarith only [hx])
  have hxi : (i:ℝ)+2=x+1 := by dsimp only [x]; ring
  dsimp only [lo,hi]
  rw [hxi]
  change _ ≤ (2*Real.log (x+1)-_)-(2*Real.log x-_) ∧ _ ≤ _
  constructor <;> linarith only [hu,hl,hfrac]

private theorem integral_cell_constant (N i : ℕ) (c : ℝ) :
    (∫ _ : ℝ in conductorThetaCell N i, c) = (hi N i-lo N i)*c := by
  have hl : 0 ≤ hi N i-lo N i :=
    (by positivity : 0 ≤ 2/((i:ℝ)+2)).trans (cell_length N i).1
  rw [setIntegral_const,conductorThetaCell,Real.volume_real_Ioc,max_eq_left hl,smul_eq_mul]

private theorem cell_const_integrable (N i : ℕ) (d : ℝ) :
    IntegrableOn (fun _ : ℝ => d) (conductorThetaCell N i) :=
  (continuousOn_const.integrableOn_Icc (a := lo N i) (b := hi N i)).mono_set Ioc_subset_Icc_self

private theorem mass_le {D : ℝ} {N i : ℕ} (hd : ∀ x ∈ conductorThetaCell N i, thetaCuspFullSource x ≤ D) :
    conductorThetaMass N i ≤ (hi N i-lo N i)*D := by
  rw [← integral_cell_constant]
  exact setIntegral_mono_on phi_integrable.integrableOn
    (cell_const_integrable N i _)
    measurableSet_Ioc hd

private theorem le_mass {d : ℝ} {N i : ℕ} (hd : ∀ x ∈ conductorThetaCell N i, d ≤ thetaCuspFullSource x) :
    (hi N i-lo N i)*d ≤ conductorThetaMass N i := by
  rw [← integral_cell_constant]
  exact setIntegral_mono_on (cell_const_integrable N i _)
    phi_integrable.integrableOn measurableSet_Ioc hd

private theorem positive_cell_envelope : ∃ C : ℝ, 0 < C ∧ ∀ {N i : ℕ}, 0 < N →
    conductorThetaMass N i ≤ (4*C)*((i:ℝ)+2)^2/(N:ℝ)^3 := by
  obtain ⟨C,hC,h⟩ := thetaCuspFullSource_superexponential_envelope (3/2)
  refine ⟨C,hC,fun {N i} hN => ?_⟩
  let y := (i:ℝ)+2
  have hy : 0 < y := by dsimp only [y]; positivity
  have hN₀ : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have he : Real.exp ((3/2)*hi N i) = y^3/(N:ℝ)^3 := by
    change Real.exp ((3/2)*(2*Real.log y-2*Real.log N))=_
    rw [show (3/2:ℝ)*(2*Real.log y-2*Real.log N)=
        (Real.log y-Real.log N)+(Real.log y-Real.log N)+(Real.log y-Real.log N) by ring,
      Real.exp_add,Real.exp_add,Real.exp_sub,Real.exp_log hy,Real.exp_log hN₀]
    ring
  have hbound (x : ℝ) (hx : x ∈ conductorThetaCell N i) :
      thetaCuspFullSource x ≤ C*(y^3/(N:ℝ)^3) := by
    rw [← he]
    exact (h x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      linarith only [neg_abs_le x,hx.2])) hC.le)
  exact (mass_le hbound).trans ((mul_le_mul_of_nonneg_right (cell_length N i).2
    (show 0 ≤ C*(y^3/(N:ℝ)^3) by positivity)).trans_eq (by change 4/y*_=4*C*y^2/_; field_simp; ring))

/-- One multiplier makes every central conductor compulsory while keeping
the integer ceiling of every raw weight globally bounded. -/
theorem square_conductor_theta_weight_bounds : ∃ (A : ℝ) (K : ℕ), 0 < A ∧
    ∀ {N : ℕ}, 2 ≤ N → ∀ i : ℕ, 0 ≤ conductorThetaWeight A N i ∧
      conductorThetaWeight A N i ≤ (K:ℝ) ∧
      (N ≤ i+2 → i+2 ≤ 2*N → 1 ≤ conductorThetaWeight A N i) := by
  have hne : (Icc (-2:ℝ) 2).Nonempty := ⟨0,by norm_num,by norm_num⟩
  obtain ⟨v,hv,hmin⟩ := isCompact_Icc.exists_isMinOn hne contDiff_thetaCuspFullSource.continuous.continuousOn
  let c := thetaCuspFullSource v
  have hc : 0 < c := thetaCuspFullSource_pos v
  let A := 4/c
  have hA : 0 < A := div_pos (by norm_num) hc
  obtain ⟨C,hC,hupper⟩ := positive_cell_envelope
  refine ⟨A,⌈A*(4*C)⌉₊,hA,fun {N} hn i => ?_⟩
  let x := (i:ℝ)+1
  let y := (i:ℝ)+2
  have hn₂ : (2:ℝ) ≤ N := by exact_mod_cast hn
  have hn₀ : (0:ℝ)<N := by linarith only [hn₂]
  have hx : 0 < x := by dsimp only [x]; positivity
  have hy : 0 < y := by dsimp only [y]; positivity
  have he : y=x+1 := by dsimp only [x,y]; ring
  change 0 ≤ A*(N:ℝ)^3*conductorThetaMass N i/y^2 ∧ _ ∧ _
  refine ⟨by have h := conductorThetaMass_nonneg N i; positivity,?_,?_⟩
  · change A*(N:ℝ)^3*conductorThetaMass N i/y^2 ≤ _
    refine le_trans ?_ (Nat.le_ceil _)
    have hh := hupper (i := i) (Nat.cast_pos.mp hn₀)
    calc _ ≤ A*(N:ℝ)^3*((4*C)*y^2/(N:ℝ)^3)/y^2 := by gcongr
         _ = A*(4*C) := by field_simp
  · intro hlow hhigh
    have h₁ : (N:ℝ) ≤ y := by exact_mod_cast hlow
    have h₂ : y ≤ 2*(N:ℝ) := by exact_mod_cast hhigh
    have hr : (N:ℝ)/2 ≤ x := by linarith only [he,h₁,hn₂]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hl := Real.log_le_log (div_pos hn₀ two_pos) hr
    have hu := Real.log_le_log hy h₂
    rw [Real.log_div hn₀.ne' two_ne_zero] at hl
    rw [Real.log_mul two_ne_zero hn₀.ne'] at hu
    have hband (u : ℝ) (hu' : u ∈ conductorThetaCell N i) : u ∈ Icc (-2:ℝ) 2 := by
      change 2*Real.log x-2*Real.log N < u ∧ u ≤ 2*Real.log y-2*Real.log N at hu'
      constructor <;> linarith only [hl,hu,hu'.1,hu'.2,hlog]
    have hm := le_mass (fun u hu' => hmin (hband u hu'))
    have hlen : 2/y*c ≤ conductorThetaMass N i :=
      (mul_le_mul_of_nonneg_right (cell_length N i).1 hc.le).trans hm
    change 1 ≤ A*(N:ℝ)^3*conductorThetaMass N i/y^2
    apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
    have hpow := pow_le_pow_left₀ hy.le h₂ 3
    have h₃ : y^2 ≤ A*(N:ℝ)^3*(2/y*c) := by
      rw [show A*(N:ℝ)^3*(2/y*c)=8*(N:ℝ)^3/y by dsimp only [A]; field_simp; ring]
      apply (le_div_iff₀ hy).mpr
      linarith only [hpow]
    exact (by simpa only [one_mul] using h₃).trans (mul_le_mul_of_nonneg_left hlen (by positivity))

/-- Right endpoint after the first i adjacent theta cells. -/
def conductorThetaEdge (N i : ℕ) := 2*Real.log ((i:ℝ)+1)-2*Real.log N

private theorem edge_succ (N i : ℕ) : conductorThetaEdge N (i+1)=hi N i := by
  unfold conductorThetaEdge
  push_cast
  rw [show (i:ℝ)+1+1=(i:ℝ)+2 by ring]

/-- Integration over complete adjacent cells has exactly two boundary terms. -/
theorem integral_over_conductorThetaCells (N M : ℕ) {f : ℝ → ℝ} (hf : Integrable f) :
    ∑ i ∈ Finset.range M, (∫ x in conductorThetaCell N i, f x) =
      ∫ x in Set.Ioc (conductorThetaEdge N 0) (conductorThetaEdge N M), f x := by
  have hstep (i : ℕ) : conductorThetaEdge N i ≤ conductorThetaEdge N (i+1) := by
    rw [edge_succ]
    change lo N i ≤ hi N i
    exact sub_nonneg.mp ((by positivity : 0 ≤ 2/((i:ℝ)+2)).trans (cell_length N i).1)
  have hmono := monotone_nat_of_le_succ hstep
  have hcell (i : ℕ) : conductorThetaCell N i=Set.Ioc (conductorThetaEdge N i) (conductorThetaEdge N (i+1)) := by
    rw [edge_succ]; rfl
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,hcell,← intervalIntegral.integral_of_le (hmono (Nat.zero_le M)),
      ← intervalIntegral.integral_of_le (hstep M),← intervalIntegral.integral_of_le (hmono (Nat.zero_le (M+1)))]
    exact intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable

theorem sum_conductorThetaMass_le (N M : ℕ) :
    ∑ i ∈ Finset.range M, conductorThetaMass N i ≤ ∫ x : ℝ, thetaCuspFullSource x := by
  simp only [conductorThetaMass,integral_over_conductorThetaCells N M phi_integrable]
  exact setIntegral_le_integral phi_integrable (ae_of_all _ fun x => (thetaCuspFullSource_pos x).le)

#print axioms square_conductor_theta_weight_bounds

end GaloisForLFunctions.CountingHolography.Sections
