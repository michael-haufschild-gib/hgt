import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.BothSignsOfTheReciprocalPrimeOctave
import GaloisForLFunctions.RHTower.BourgainPartialSummation
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdProductOnOneMangoldtOctave

/-!
# Sampling reciprocal prime octaves at powers

The sum of either sign on all integer endpoints is controlled by its
values on the power grid. Each moving boundary charges the Mangoldt
mass it crosses once. Abel summation bounds the total interpolation
cost by one largest grid interval.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Unweighted sign mass on the actual intervals (m^r,2m^r]. -/
def powerOctaveSignMass (ε : ℝ) (r K : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 K,max (ε*reciprocalOctaveError (2*m^r)) 0

private def gridMangoldtMass (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N,vonMangoldt d
private def gridReciprocalMass (N : ℕ) : ℝ := ∑ d ∈ Ioc 0 N,vonMangoldt d/(d:ℝ)

private theorem grid_mass_bound (N : ℕ) : gridMangoldtMass N ≤ 7*(N:ℝ) := by
  have hi : Ioc 0 N=Icc 1 N := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  simpa only [gridMangoldtMass,hi] using _root_.RHTower.sum_vonMangoldt_Icc_le_seven N

private theorem grid_prefix_diff (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ d ∈ Ioc 0 b,f d)-(∑ d ∈ Ioc 0 a,f d)=∑ d ∈ Ioc a b,f d := by
  linarith only [sum_Ioc_consecutive f (Nat.zero_le a) hab]

private theorem grid_mass_mono : Monotone gridMangoldtMass := by
  intro a b hab
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl hab) (fun _ _ _ => vonMangoldt_nonneg)

private theorem grid_reciprocal_diff {l a b : ℕ} (hl : 0 < l) (hla : l ≤ a) (hab : a ≤ b) :
    0 ≤ gridReciprocalMass b-gridReciprocalMass a ∧
    gridReciprocalMass b-gridReciprocalMass a ≤ (gridMangoldtMass b-gridMangoldtMass a)/(l:ℝ) := by
  simp only [gridReciprocalMass,gridMangoldtMass,grid_prefix_diff _ hab,sum_div]
  refine ⟨sum_nonneg (fun d _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)),?_⟩
  apply sum_le_sum
  intro d hd
  exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Nat.cast_pos.mpr hl)
    (Nat.cast_le.mpr (hla.trans (mem_Ioc.mp hd).1.le))

private theorem grid_octave_value (n : ℕ) : reciprocalOctaveError n =
    gridReciprocalMass n-gridReciprocalMass (n/2)-Real.log 2 := by
  rw [reciprocalOctaveError,gridReciprocalMass,gridReciprocalMass,grid_prefix_diff _ (Nat.div_le_self n 2)]

/-- The two genuine prime intervals traversed between a sample and the
right endpoint bound the total change across the cell. -/
private theorem change_on_grid_cell {l h n : ℕ} (hl : 0 < l) (hlo : 2*l ≤ n) (hhi : n ≤ 2*h) :
    |reciprocalOctaveError n-reciprocalOctaveError (2*h)| ≤
      ((gridMangoldtMass (2*h)+gridMangoldtMass h)-(gridMangoldtMass (2*l)+gridMangoldtMass l))/(l:ℝ) := by
  have hnl : l ≤ n/2 := by omega
  have hnh : n/2 ≤ h := by omega
  have htop := grid_reciprocal_diff hl (by omega : l ≤ n) hhi
  have hbot := grid_reciprocal_diff hl hnl hnh
  have ht := div_le_div_of_nonneg_right (sub_le_sub_left (grid_mass_mono hlo) (gridMangoldtMass (2*h))) (Nat.cast_nonneg l : 0 ≤ (l:ℝ))
  have hb := div_le_div_of_nonneg_right (sub_le_sub_left (grid_mass_mono hnl) (gridMangoldtMass h)) (Nat.cast_nonneg l : 0 ≤ (l:ℝ))
  rw [grid_octave_value,grid_octave_value,show 2*h/2=h by omega,abs_le]
  have rhs : ((gridMangoldtMass (2*h)+gridMangoldtMass h)-(gridMangoldtMass (2*l)+gridMangoldtMass l))/(l:ℝ) =
      (gridMangoldtMass (2*h)-gridMangoldtMass (2*l))/(l:ℝ)+(gridMangoldtMass h-gridMangoldtMass l)/(l:ℝ) := by ring
  rw [rhs]
  constructor <;> linarith only [htop.1,htop.2,hbot.1,hbot.2,ht,hb]

private theorem positive_part_change {ε : ℝ} (he : |ε|=1) (a b : ℝ) :
    max (ε*a) 0 ≤ max (ε*b) 0+|a-b| := by
  have hh := le_abs_self (ε*(a-b))
  rw [abs_mul,he,one_mul] at hh
  exact max_le (by linarith only [hh,le_max_left (ε*b) 0]) (add_nonneg (le_max_right _ _) (abs_nonneg _))

private def powerGridMass (r m : ℕ) := gridMangoldtMass (2*m^r)+gridMangoldtMass (m^r)

private theorem power_grid_mass_bound (r m : ℕ) : powerGridMass r m ≤ 21*(m:ℝ)^r := by
  have h := add_le_add (grid_mass_bound (2*m^r)) (grid_mass_bound (m^r))
  simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] at h
  exact h.trans_eq (by ring)

private theorem power_grid_mass_monotone (r : ℕ) : Monotone (powerGridMass r) := by
  intro a b h
  have hp := Nat.pow_le_pow_left h r
  exact add_le_add (grid_mass_mono (Nat.mul_le_mul_left 2 hp)) (grid_mass_mono hp)

private theorem power_grid_initial {r : ℕ} (hr : 0 < r) : powerGridMass r 0=0 := by
  simp [powerGridMass,gridMangoldtMass,zero_pow hr.ne']

/-- Abel summation of all the cell charges at once. -/
private theorem weighted_power_grid_jumps (s K : ℕ) :
    (∑ m ∈ Icc 1 K,(powerGridMass (s+2) m-powerGridMass (s+2) (m-1))/(m:ℝ)) ≤ 42*(K:ℝ)^(s+1) := by
  let F := powerGridMass (s+2)
  let a (m : ℕ) := F m-F (m-1)
  have hF0 : F 0=0 := power_grid_initial (by omega)
  have hprefix (m : ℕ) : ∑ j ∈ Icc 1 m,a j=F m := by
    induction m with
    | zero => simp [hF0]
    | succ m ih =>
      rw [sum_Icc_succ_top (show 1 ≤ m+1 by omega),ih]
      simp only [a,Nat.add_sub_cancel]; ring
  have hab := sum_smul_eq_prefix_differences a (fun m : ℕ => (m:ℝ)⁻¹) K
  simp only [smul_eq_mul,hprefix,Nat.cast_succ] at hab
  have hr (m : ℕ) (hm : m∈Icc 1 K) :
      F m*((m:ℝ)⁻¹-((m:ℝ)+1)⁻¹) ≤ 21*(K:ℝ)^s := by
    have hm0 : 0 < (m:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hm).1
    have hd : (m:ℝ)⁻¹-((m:ℝ)+1)⁻¹ = ((m:ℝ)*((m:ℝ)+1))⁻¹ := by
      field_simp [hm0.ne',(by positivity : (m:ℝ)+1≠0)]
      ring
    rw [hd,←div_eq_mul_inv]
    apply (div_le_iff₀ (mul_pos hm0 (by positivity))).mpr
    calc F m ≤ 21*(m:ℝ)^(s+2) := power_grid_mass_bound _ _
         _ = (21*(m:ℝ)^s)*((m:ℝ)*(m:ℝ)) := by ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left
           (pow_le_pow_left₀ hm0.le (Nat.cast_le.mpr (mem_Icc.mp hm).2) s) (by norm_num))
           (mul_le_mul_of_nonneg_left (by linarith : (m:ℝ) ≤ m+1) hm0.le) (by positivity) (by positivity)
  have htop : F K*((K:ℝ)+1)⁻¹ ≤ 21*(K:ℝ)^(s+1) := by
    rw [←div_eq_mul_inv,div_le_iff₀ (by positivity)]
    apply (power_grid_mass_bound _ _).trans
    rw [show s+2=(s+1)+1 by omega,pow_succ]
    have h := mul_le_mul_of_nonneg_left (by linarith : (K:ℝ) ≤ K+1) (by positivity : 0 ≤ 21*(K:ℝ)^(s+1))
    linarith only [h]
  have hs := sum_le_sum hr
  rw [sum_const,nsmul_eq_mul,show (Icc 1 K).card=K by simp [Nat.card_Icc]] at hs
  change (∑ m ∈ Icc 1 K,a m/(m:ℝ)) ≤ _
  simp only [div_eq_mul_inv]
  rw [hab]
  rw [pow_succ (K:ℝ) s] at htop ⊢
  linarith only [htop,hs]

private theorem mesh_power_gap (m k : ℕ) :
    (m+1)^(k+1) ≤ m^(k+1)+(k+1)*(m+1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (m+1)^(k+1+1) = (m+1)^(k+1)*m+(m+1)^(k+1) := by rw [pow_succ (m+1) (k+1)]; ring
         _ ≤ (m^(k+1)+(k+1)*(m+1)^k)*m+(m+1)^(k+1) :=
           Nat.add_le_add_right (Nat.mul_le_mul_right m ih) _
         _ ≤ _ := by
           have h := Nat.mul_le_mul_left ((k+1)*(m+1)^k) (Nat.le_succ m)
           simp only [pow_succ] at *
           nlinarith only [h]

private theorem sparse_grid_cell {ε : ℝ} (he : |ε|=1) (s : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    (∑ n ∈ Ioc (2*(m-1)^(s+2)) (2*m^(s+2)),max (ε*reciprocalOctaveError n) 0) ≤
      (2*((s:ℝ)+2))*(m:ℝ)^(s+1)*max (ε*reciprocalOctaveError (2*m^(s+2))) 0 +
      (2*((s:ℝ)+2)*(2:ℝ)^(s+2))*((powerGridMass (s+2) m-powerGridMass (s+2) (m-1))/(m:ℝ)) := by
  let b := m-1
  let r := s+2
  let D := 2*m^r-2*b^r
  let E := powerGridMass r m-powerGridMass r b
  let Z := max (ε*reciprocalOctaveError (2*m^r)) 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hb : 0 < b := by dsimp only [b]; omega
  have hm' : m=b+1 := by dsimp only [b]; omega
  have hm0 : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have hb0 : 0 < (b:ℝ) := Nat.cast_pos.mpr hb
  have hE : 0 ≤ E := sub_nonneg.mpr (power_grid_mass_monotone r (show b ≤ m by omega))
  have hgap := mesh_power_gap b (s+1)
  rw [←hm'] at hgap
  have hD : (D:ℝ) ≤ (2*((s:ℝ)+2))*(m:ℝ)^(s+1) := by
    have hnat : D ≤ (2*(s+2))*m^(s+1) := by
      have hg : 2*m^(s+2) ≤ 2*b^(s+2)+(2*(s+2))*m^(s+1) := calc
        _ ≤ 2*(b^(s+2)+(s+2)*m^(s+1)) := Nat.mul_le_mul_left 2 hgap
        _ = _ := by ring
      dsimp only [D,r]
      omega
    exact_mod_cast hnat
  have hpow : (m:ℝ)^r ≤ (2:ℝ)^r*(b:ℝ)^r := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ hm0.le (by exact_mod_cast (show m ≤ 2*b by omega)) _
  have hdiv : 1/(b:ℝ)^r ≤ (2:ℝ)^r/(m:ℝ)^r :=
    (div_le_div_iff₀ (pow_pos hb0 _) (pow_pos hm0 _)).mpr (by simpa only [one_mul] using hpow)
  have hr (n : ℕ) (hn : n∈Ioc (2*b^r) (2*m^r)) :
      max (ε*reciprocalOctaveError n) 0 ≤ Z+E/(b:ℝ)^r := by
    have hc := change_on_grid_cell (Nat.pow_pos hb) (mem_Ioc.mp hn).1.le (mem_Ioc.mp hn).2
    rw [Nat.cast_pow] at hc
    exact (positive_part_change he _ (reciprocalOctaveError (2*m^r))).trans (add_le_add le_rfl hc)
  have hu := sum_le_sum hr
  rw [sum_const,nsmul_eq_mul,Nat.card_Ioc] at hu
  change _ ≤ (D:ℝ)*(Z+E/(b:ℝ)^r) at hu
  apply hu.trans
  rw [mul_add]
  apply add_le_add (mul_le_mul_of_nonneg_right hD hZ)
  have hdE := mul_le_mul_of_nonneg_left hdiv hE
  calc (D:ℝ)*(E/(b:ℝ)^r) =
        (D:ℝ)*(E*(1/(b:ℝ)^r)) := by ring
       _ ≤ (2*((s:ℝ)+2)*(m:ℝ)^(s+1))*(E*((2:ℝ)^r/(m:ℝ)^r)) :=
         mul_le_mul hD hdE (by positivity) (by positivity)
       _ = _ := by
         change _ = (2*((s:ℝ)+2)*(2:ℝ)^r)*(E/(m:ℝ))
         dsimp only [r]; rw [pow_succ (m:ℝ) (s+1)]
         field_simp [hm0.ne']

private theorem sum_power_grid_cells (f : ℕ → ℝ) (r : ℕ) {K : ℕ} (hK : 0 < K) :
    (∑ n ∈ Icc 1 (2*K^r),f n) = (∑ n ∈ Icc 1 2,f n) +
      ∑ m ∈ Icc 2 K, ∑ n ∈ Ioc (2*(m-1)^r) (2*m^r),f n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  clear hK
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_Icc_succ_top (show 2 ≤ j+1+1 by omega)]
    have hs := sum_Ioc_consecutive f (Nat.zero_le (2*(j+1)^r))
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_succ (j+1)) r))
    have hi (A : ℕ) : Ioc 0 A=Icc 1 A := by ext i; simp only [mem_Ioc,mem_Icc]; omega
    rw [hi,hi,ih] at hs
    simp only [Nat.add_sub_cancel]
    linarith only [hs]

/-- One largest grid interval pays the total interpolation error, and
the rest uses only the unweighted sampled sign mass. -/
theorem sign_mass_on_power_grid (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, |ε|=1 →
    ∀ K : ℕ, 0 < K →
    (∑ n ∈ Icc 1 (2*K^(s+2)),max (ε*reciprocalOctaveError n) 0) ≤
      C*(K:ℝ)^(s+1)*(1+powerOctaveSignMass ε (s+2) K) := by
  let A := 2*((s:ℝ)+2)
  let B := A*(2:ℝ)^(s+2)
  let H := ∑ n ∈ Icc 1 2,|reciprocalOctaveError n|
  have hH : 0 ≤ H := sum_nonneg (fun n _ => abs_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨H+A+42*B,by positivity,fun {ε} he K hK => ?_⟩
  let r := s+2
  let Z (m : ℕ) := max (ε*reciprocalOctaveError (2*m^r)) 0
  let E (m : ℕ) := (powerGridMass r m-powerGridMass r (m-1))/(m:ℝ)
  let X := (K:ℝ)^(s+1)
  let S := powerOctaveSignMass ε r K
  have hX : 1 ≤ X := one_le_pow₀ (Nat.one_le_cast.mpr hK)
  have hS : 0 ≤ S := sum_nonneg (fun m _ => le_max_right _ _)
  have hs : Icc 2 K ⊆ Icc 1 K := Icc_subset_Icc (by decide) le_rfl
  have hE (m : ℕ) : 0 ≤ E m := div_nonneg (sub_nonneg.mpr (power_grid_mass_monotone r (Nat.sub_le _ _))) (Nat.cast_nonneg _)
  have h₁ : (∑ n ∈ Icc 1 2,max (ε*reciprocalOctaveError n) 0) ≤ H := by
    apply sum_le_sum
    intro n _
    apply max_le _ (abs_nonneg _)
    exact (le_abs_self _).trans_eq (by rw [abs_mul,he,one_mul])
  have hx (m : ℕ) (hm : m∈Icc 2 K) :
      (∑ n ∈ Ioc (2*(m-1)^r) (2*m^r),max (ε*reciprocalOctaveError n) 0) ≤ A*X*Z m+B*E m := by
    apply (sparse_grid_cell he s (mem_Icc.mp hm).1).trans
    apply add_le_add _ le_rfl
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (mem_Icc.mp hm).2) _) hA) (le_max_right _ _)
  have hup := sum_le_sum hx
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hup
  have hsz := sum_le_sum_of_subset_of_nonneg (f := Z) hs (fun _ _ _ => le_max_right _ _)
  have hse := (sum_le_sum_of_subset_of_nonneg (f := E) hs (fun m _ _ => hE m)).trans (weighted_power_grid_jumps s K)
  have ht := hup.trans (add_le_add (mul_le_mul_of_nonneg_left hsz (mul_nonneg hA (zero_le_one.trans hX)))
    (mul_le_mul_of_nonneg_left hse hB))
  rw [sum_power_grid_cells _ r hK]
  apply (add_le_add h₁ ht).trans
  change H+(A*X*S+B*(42*X)) ≤ (H+A+42*B)*X*(1+S)
  have h₀ := le_mul_of_one_le_right hH hX
  have hnon := mul_nonneg (mul_nonneg (add_nonneg hH (mul_nonneg (by norm_num : (0:ℝ) ≤ 42) hB))
    (zero_le_one.trans hX)) hS
  linarith only [h₀,hnon,mul_nonneg hA (zero_le_one.trans hX)]

#print axioms sign_mass_on_power_grid

open Filter in
/-- A cofinal budget on a polynomial grid bounds every actual zero,
including between the sampled prime octaves. -/
theorem zero_abscissa_of_power_grid_budget (s : ℕ) {ε δ : ℝ} (he : |ε|=1) (hδ : 0 ≤ δ)
    (h : ∃ A : ℝ, ∃ᶠ K : ℕ in atTop, powerOctaveSignMass ε (s+2) K ≤ A*(K:ℝ)^δ) :
    _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1+δ)/((s:ℝ)+2) := by
  let b := ((s:ℝ)+1+δ)/((s:ℝ)+2)
  have hr : 0 < (s:ℝ)+2 := by positivity
  have hb : 1/2 ≤ b := (le_div_iff₀ hr).mpr (by linarith only [hδ,(Nat.cast_nonneg s : (0:ℝ) ≤ s)])
  obtain ⟨A,hA⟩ := h
  obtain ⟨C,hC,hgrid⟩ := sign_mass_on_power_grid s
  apply zero_abscissa_of_cofinal_reciprocal_octave_mass hb he
  refine ⟨C*(1+max A 0),frequently_atTop.mpr fun L => ?_⟩
  obtain ⟨K,hK,hs⟩ := frequently_atTop.mp hA (max 1 L)
  have hK1 : 1 ≤ K := (le_max_left ..).trans hK
  have hk0 : (0:ℝ) < K := Nat.cast_pos.mpr hK1
  have hk1 : (1:ℝ) ≤ K := Nat.one_le_cast.mpr hK1
  have hkpow : K ≤ K^(s+2) := calc K = K*1 := (Nat.mul_one _).symm
                                   _ ≤ K*K^(s+1) := Nat.mul_le_mul_left _ (one_le_pow₀ hK1)
                                   _ = _ := by rw [pow_succ]; ring
  let N := 2*K^(s+2)
  have hLN : L ≤ N := ((le_max_right ..).trans hK).trans (hkpow.trans (by dsimp only [N]; omega))
  refine ⟨N,hLN,?_⟩
  have hζ := hgrid he K hK1
  have hclip : reciprocalOctaveSignMass ε N ≤ ∑ n ∈ Icc 1 N,max (ε*reciprocalOctaveError n) 0 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => le_max_right _ _)
  have hh := hs.trans (mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.rpow_nonneg hk0.le _))
  have hu : 1+powerOctaveSignMass ε (s+2) K ≤ (1+max A 0)*(K:ℝ)^δ := by
    linarith only [hh,Real.one_le_rpow hk1 hδ]
  have hfactor : (K:ℝ)^(s+1)*(K:ℝ)^δ ≤ (N:ℝ)^b := by
    rw [←Real.rpow_natCast (K:ℝ) (s+1),←Real.rpow_add hk0,Nat.cast_succ]
    have heq : ((s:ℝ)+2)*b=(s:ℝ)+1+δ := by dsimp only [b]; field_simp
    rw [←heq,Real.rpow_mul hk0.le,show (s:ℝ)+2=((s+2:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast]
    apply Real.rpow_le_rpow (pow_nonneg hk0.le _)
    · exact_mod_cast (show K^(s+2) ≤ N by dsimp only [N]; omega)
    · linarith only [hb]
  have hca : 0 ≤ C*(1+max A 0) := mul_nonneg hC (by linarith only [le_max_right A 0])
  calc reciprocalOctaveSignMass ε N ≤ _ := hclip.trans hζ
       _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC (pow_nonneg hk0.le _))
       _ = (C*(1+max A 0))*((K:ℝ)^(s+1)*(K:ℝ)^δ) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hfactor hca

open Filter in
/-- Subpower mass on arbitrarily late powers of each requested accuracy. -/
def subpowerOctaveGrid (r : ℕ) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∃ᶠ K : ℕ in atTop, powerOctaveSignMass ε r K ≤ A*(K:ℝ)^δ

theorem zero_abscissa_of_subpower_octave_grid (s : ℕ) {ε : ℝ} (he : |ε|=1)
    (h : subpowerOctaveGrid (s+2) ε) : _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) := by
  by_contra! hb
  have hr : 0 < (s:ℝ)+2 := by positivity
  have hgap := (div_lt_iff₀ hr).mp hb
  let δ := (_root_.RHTower.zetaZeroAbscissa*((s:ℝ)+2)-((s:ℝ)+1))/2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hgap)
  have hh := (le_div_iff₀ hr).mp (zero_abscissa_of_power_grid_budget s he hδ.le (h δ hδ))
  dsimp only [δ] at hh
  linarith only [hgap,hh]

/-- Total negative error on the sparse sixth powers suffices for the
eleven-thirds bound on every terminal of the original conductor prefix. -/
theorem eleven_thirds_of_sixth_power_octaves (h : subpowerOctaveGrid 6 (-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) := by
  apply five_sixths_iff_seventeenNinthsConductorPrefix.mp
  convert zero_abscissa_of_subpower_octave_grid 4 (by norm_num : |(-1:ℝ)|=1) h using 1
  norm_num

#print axioms zero_abscissa_of_power_grid_budget
#print axioms eleven_thirds_of_sixth_power_octaves

private theorem grid_mass_value (n : ℕ) : gridMangoldtMass n=Chebyshev.psi n := by
  simp only [gridMangoldtMass,Chebyshev.psi,Nat.floor_natCast]

private theorem even_octave_pointwise_above_width {t : ℝ} (ht : _root_.RHTower.zeroReSup < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ,1 ≤ m → |reciprocalOctaveError (2*m)| ≤ B*(m:ℝ)^(t-1) := by
  obtain ⟨C,hC,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow ht
  have ht0 : 0 ≤ t := by linarith only [_root_.RHTower.half_le_zeroReSup,ht]
  refine ⟨2*C*(2:ℝ)^t+2,by positivity,fun m hm => ?_⟩
  have hm0 : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  let a (n : ℕ) : ℝ := vonMangoldt n-1
  have hP (n : ℕ) (hn : n∈Ioc m (2*m)) :
      |∑ d ∈ Ioc m n,a d| ≤ 2*C*(2*(m:ℝ))^t := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
    have hs : (∑ d ∈ Ioc m n,a d)=(Chebyshev.psi n-n)-(Chebyshev.psi m-m) := by
      have hv : (∑ d ∈ Ioc m n,vonMangoldt d)=Chebyshev.psi n-Chebyshev.psi m := by
        rw [←grid_mass_value,←grid_mass_value]
        exact (grid_prefix_diff _ hl.le).symm
      dsimp only [a]
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,Nat.cast_sub hl.le,hv]
      ring
    rw [hs]
    have h1 := (hψ n (Nat.one_le_cast.mpr (hm.trans hl.le))).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hu : (n:ℝ) ≤ 2*m) ht0) hC)
    have h2 := (hψ m (Nat.one_le_cast.mpr hm)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hm0.le (by linarith only [hm0] : (m:ℝ) ≤ 2*m) ht0) hC)
    linarith only [h1,h2,abs_sub (Chebyshev.psi n-n) (Chebyshev.psi m-m)]
  have hc := _root_.RHTower.norm_sum_Ioc_weight_mul_le (fun d => ((a d:ℝ):ℂ)) (fun d => (d:ℝ)⁻¹)
    (show m < 2*m by omega) (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun n hn => inv_anti₀ (Nat.cast_pos.mpr (hm.trans (mem_Ioc.mp hn).1.le)) (Nat.cast_le.mpr (Nat.le_succ n)))
    (fun n hn => by simpa only [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] using hP n hn)
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,Nat.cast_succ] at hc
  have hlog := _root_.HTGeometry.abs_sum_Ioc_inv_sub_log_le hm (show m ≤ 2*m by omega)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hm0.ne',add_sub_cancel_right] at hlog
  let U := ∑ d ∈ Ioc m (2*m),(d:ℝ)⁻¹*a d
  let V := (∑ d ∈ Ioc m (2*m),(d:ℝ)⁻¹)-Real.log 2
  have hsplit : reciprocalOctaveError (2*m)=U+V := by
    rw [reciprocalOctaveError,show 2*m/2=m by omega]
    dsimp only [U,V,a]
    have he (d : ℕ) : (d:ℝ)⁻¹*(vonMangoldt d-1)+ (d:ℝ)⁻¹=vonMangoldt d/(d:ℝ) := by ring
    rw [←add_sub_assoc,←sum_add_distrib,sum_congr rfl (fun d _ => he d)]
  have hu := hc.trans (mul_le_mul_of_nonneg_left (inv_anti₀ hm0 (by linarith : (m:ℝ) ≤ m+1)) (by positivity))
  have hv := hlog.trans (add_le_add (one_div_le_one_div_of_le hm0 (by linarith : (m:ℝ) ≤ 2*m)) (le_refl (1/(m:ℝ))))
  have hscale := Real.one_le_rpow (Nat.one_le_cast.mpr hm : (1:ℝ) ≤ m) ht0
  rw [hsplit]
  apply ((abs_add_le U V).trans (add_le_add hu hv)).trans
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hm0.le,Real.rpow_sub_one hm0.ne']
  have hsc := mul_le_mul_of_nonneg_right hscale (inv_nonneg.mpr hm0.le)
  simp only [div_eq_mul_inv] at hsc ⊢
  linarith only [hsc]

private theorem root_sum_shift (f : ℕ → ℝ) (K : ℕ) :
    (∑ m ∈ Icc 1 K,f m)=∑ i ∈ range K,f (i+1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_Icc_succ_top (show 1 ≤ K+1 by omega),Finset.sum_range_succ,ih]

private theorem subpower_grid_of_zeroReSup (s : ℕ) {ε : ℝ} (he : |ε|=1)
    (hΘ : _root_.RHTower.zeroReSup ≤ ((s:ℝ)+1)/((s:ℝ)+2)) : subpowerOctaveGrid (s+2) ε := by
  intro δ hδ
  let r := s+2
  let t := ((s:ℝ)+1+δ)/((s:ℝ)+2)
  have hr : 0 < (s:ℝ)+2 := by positivity
  have ht : _root_.RHTower.zeroReSup < t := hΘ.trans_lt ((div_lt_div_iff_of_pos_right hr).mpr (by linarith only [hδ]))
  obtain ⟨B,hB,h⟩ := even_octave_pointwise_above_width ht
  have hg : (r:ℝ)*(t-1)=δ-1 := by
    dsimp only [r,t]; push_cast; field_simp [hr.ne']; ring
  refine ⟨B*(1+1/δ)*(2:ℝ)^δ,Filter.Eventually.frequently ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with K hK
  have row (m : ℕ) (hm : m∈Icc 1 K) : max (ε*reciprocalOctaveError (2*m^r)) 0 ≤ B*(m:ℝ)^(δ-1) := by
    have hm1 := (mem_Icc.mp hm).1
    have hb := h (m^r) (one_le_pow₀ hm1)
    rw [Nat.cast_pow,←Real.rpow_natCast (m:ℝ) r,←Real.rpow_mul (Nat.cast_nonneg m),hg] at hb
    apply max_le _ (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    exact (le_abs_self _).trans (by rwa [abs_mul,he,one_mul])
  have hs := sum_le_sum row
  rw [←mul_sum,root_sum_shift (fun m : ℕ => (m:ℝ)^(δ-1))] at hs
  simp only [Nat.cast_succ] at hs
  have ht := _root_.GaloisForLFunctions.ArithmeticGaugeTheory.sum_rpow_sub_one_le hδ K
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (K:ℝ)+1)
    (by linarith only [(Nat.one_le_cast.mpr hK : (1:ℝ) ≤ K)] : (K:ℝ)+1 ≤ 2*K) hδ.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg _)] at hpow
  exact hs.trans ((mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hpow (by positivity))) hB).trans_eq (by ring))

/-- For either sign, subpower growth of the mass sampled at m^r
is equivalent to the closed zero-free threshold 1-1/r. -/
theorem subpower_octave_grid_iff_abscissa (s : ℕ) {ε : ℝ} (he : |ε|=1) :
    subpowerOctaveGrid (s+2) ε ↔ _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) := by
  refine ⟨zero_abscissa_of_subpower_octave_grid s he,fun h => subpower_grid_of_zeroReSup s he ?_⟩
  exact _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
    (_root_.RHTower.re_le_zetaZeroAbscissa (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)).trans h

#print axioms subpower_octave_grid_iff_abscissa

/-- The Riemann hypothesis is equivalent to a cofinal subpower bound
on the unweighted negative errors at perfect-square octave endpoints. -/
theorem riemannHypothesis_iff_square_octave_deficit :
    RiemannHypothesis ↔ subpowerOctaveGrid 2 (-1) := by
  constructor
  · intro hrh
    apply subpower_grid_of_zeroReSup 0 (by norm_num)
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hrh q).le
    simpa using hsup
  · intro h
    have hw : _root_.RHTower.zetaZeroAbscissa ≤ 1/2 := by
      simpa using zero_abscissa_of_subpower_octave_grid 0 (by norm_num : |(-1:ℝ)|=1) h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hhalf _ hz
    exact (hhalf.not_ge ((_root_.RHTower.re_le_zetaZeroAbscissa hz).trans hw))

#print axioms riemannHypothesis_iff_square_octave_deficit


/-- Total normalized logarithmic shortfall of the integer gcd products,
with octave lower endpoint m^r and product horizon m^(r+1). -/
def powerGridGcdDeficit (r K : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 K,max (Real.log 2-Real.log (octaveGcdProduct (m^r) (m^(r+1)))/(m:ℝ)^(r+1)) 0

private theorem power_grid_gcd_row (r : ℕ) {m : ℕ} (hm : 0 < m) :
    let d := max (Real.log 2-Real.log (octaveGcdProduct (m^r) (m^(r+1)))/(m:ℝ)^(r+1)) 0 -
      max ((-1:ℝ)*reciprocalOctaveError (2*m^r)) 0
    0 ≤ d ∧ d ≤ 14/(m:ℝ) := by
  let M := m^r
  let X := m^(r+1)
  let A := ∑ d ∈ Ioc M (2*M),vonMangoldt d/(d:ℝ)
  let Q := Real.log (octaveGcdProduct M X)
  have hm0 : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hM : 0 < M := Nat.pow_pos hm
  have hX : 0 < (X:ℝ) := Nat.cast_pos.mpr (Nat.pow_pos hm)
  have hrow := octave_gcd_product_rounding hM X
  change 0 ≤ (X:ℝ)*A-Q ∧ (X:ℝ)*A-Q ≤ _ at hrow
  have hmass := (sum_le_sum_of_subset_of_nonneg (show Ioc M (2*M) ⊆ Ioc 0 (2*M) from
    Ioc_subset_Ioc (Nat.zero_le _) le_rfl) (fun _ _ _ => vonMangoldt_nonneg)).trans (grid_mass_bound (2*M))
  have hu := hrow.2.trans hmass
  have hratio : (14*(M:ℝ))/(X:ℝ)=14/(m:ℝ) := by
    dsimp only [M,X]; push_cast; rw [pow_succ]; field_simp [hm0.ne']
  have hlo : Q/(X:ℝ) ≤ A := (div_le_iff₀ hX).mpr (by linarith only [hrow.1])
  have hhi : A-Q/(X:ℝ) ≤ 14/(m:ℝ) := by
    rw [←hratio,←mul_div_cancel_right₀ A hX.ne',←sub_div,div_le_div_iff_of_pos_right hX]
    push_cast at hu; linarith only [hu]
  have he : reciprocalOctaveError (2*M)=A-Real.log 2 := by
    rw [reciprocalOctaveError,show 2*M/2=M by omega]
  have hxcast : (m:ℝ)^(r+1)=(X:ℝ) := (Nat.cast_pow m (r+1)).symm
  change 0 ≤ max (Real.log 2-Q/(m:ℝ)^(r+1)) 0-max (-1*reciprocalOctaveError (2*M)) 0 ∧ _
  rw [hxcast,he]
  simp only [neg_one_mul,neg_sub]
  constructor
  · exact sub_nonneg.mpr (max_le_max_right 0 (sub_le_sub_left hlo _))
  · apply (sub_le_iff_le_add).mpr
    apply max_le
    · linarith only [hhi,le_max_left (Real.log 2-A) 0]
    · exact add_nonneg (by positivity) (le_max_right _ _)

theorem sparse_gcd_deficit_comparison (r K : ℕ) :
    0 ≤ powerGridGcdDeficit r K-powerOctaveSignMass (-1) r K ∧
      powerGridGcdDeficit r K-powerOctaveSignMass (-1) r K ≤ 14*(1+Real.log K) := by
  rw [powerGridGcdDeficit,powerOctaveSignMass,←sum_sub_distrib]
  constructor
  · exact sum_nonneg (fun m hm => (power_grid_gcd_row r (mem_Icc.mp hm).1).1)
  · have h := sum_le_sum (s := Icc 1 K) (fun m hm => (power_grid_gcd_row r (mem_Icc.mp hm).1).2)
    have hh := _root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log K
    simp only [div_eq_mul_inv,←mul_sum] at h
    simp only [one_div] at hh
    exact h.trans (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 14))

open Filter in
/-- Unbounded sequences of integer product prefixes with subpower total shortfall. -/
def subpowerGcdGrid (r : ℕ) : Prop :=
  ∀ δ : ℝ,0 < δ → ∃ A : ℝ, ∃ᶠ K : ℕ in atTop,powerGridGcdDeficit r K ≤ A*(K:ℝ)^δ

open Filter in
theorem subpower_gcd_grid_iff_octave (r : ℕ) : subpowerGcdGrid r ↔ subpowerOctaveGrid r (-1) := by
  constructor
  · intro h δ hδ
    obtain ⟨A,hA⟩ := h δ hδ
    exact ⟨A,hA.mono fun K hk => (sub_nonneg.mp (sparse_gcd_deficit_comparison r K).1).trans hk⟩
  · intro h δ hδ
    obtain ⟨A,hA⟩ := h δ hδ
    refine ⟨A+14*(1+1/δ),(hA.and_eventually (eventually_ge_atTop 1)).mono ?_⟩
    rintro K ⟨hk,hK⟩
    have hk0 : (0:ℝ) < K := Nat.cast_pos.mpr hK
    have hx := Real.one_le_rpow (Nat.one_le_cast.mpr hK : (1:ℝ) ≤ K) hδ.le
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hk0 δ)
    rw [Real.log_rpow hk0] at hlog
    have hsmall : Real.log K ≤ (K:ℝ)^δ/δ := (le_div_iff₀ hδ).mpr (by linarith only [hlog])
    have he := (sparse_gcd_deficit_comparison r K).2
    calc powerGridGcdDeficit r K ≤ powerOctaveSignMass (-1) r K+14*(1+Real.log K) := by linarith only [he]
         _ ≤ A*(K:ℝ)^δ+14*((K:ℝ)^δ+(K:ℝ)^δ/δ) :=
           add_le_add hk (mul_le_mul_of_nonneg_left (add_le_add hx hsmall) (by norm_num))
         _ = _ := by ring

/-- The square/cube integer product criterion is equivalent to RH. -/
theorem riemannHypothesis_iff_square_cube_gcd_deficit :
    RiemannHypothesis ↔ subpowerGcdGrid 2 := riemannHypothesis_iff_square_octave_deficit.trans (subpower_gcd_grid_iff_octave 2).symm

/-- The sixth/seventh-power integer product criterion implies the
absolute eleven-thirds estimate at every conductor endpoint. -/
theorem eleven_thirds_of_sixth_seventh_gcd_deficit (h : subpowerGcdGrid 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) :=
  eleven_thirds_of_sixth_power_octaves ((subpower_gcd_grid_iff_octave 6).mp h)

/-- The absolute whole-prefix bound at eleven thirds also recovers
the cofinal subpower deficit for the sixth/seventh-power gcd products. -/
theorem sixth_seventh_gcd_iff_eleven_thirds :
    subpowerGcdGrid 6 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) := by
  rw [subpower_gcd_grid_iff_octave,←five_sixths_iff_seventeenNinthsConductorPrefix]
  convert subpower_octave_grid_iff_abscissa 4 (by norm_num : |(-1:ℝ)|=1) using 1 <;> norm_num

#print axioms sixth_seventh_gcd_iff_eleven_thirds
#print axioms sparse_gcd_deficit_comparison
#print axioms riemannHypothesis_iff_square_cube_gcd_deficit
#print axioms eleven_thirds_of_sixth_seventh_gcd_deficit

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
