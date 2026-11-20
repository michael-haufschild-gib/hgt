import GaloisForLFunctions.HTGeometry.DispersivePDE.TheLoadParameterOfWeightedCriticalModes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Geometric threshold for heterogeneous synchronized critical modes

Write xᵢ for the critical power of the i-th amplitude. The algebraic
system in Fan–Giaretto–Soave, Theorem 1.1, has mass power
r = (N−2)/N and equal interaction weights. With independent positive
masses and arbitrary positive weights of sum one, the same threshold
becomes the weighted geometric mean of the self-couplings. A scalar
load constructs the state. A largest-coordinate ratio compares states
across changes in any of the three coefficient families.
-/

noncomputable section
open Finset
namespace HTGeometry.WeightedCriticalModes
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Synchronized equations in the critical-power density coordinates. -/
def Synchronized (w μ m : ι → ℝ) (r b : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0<x i) ∧ ∀ i, μ i*x i=m i*(x i)^r+b*geometricMean w x

omit [Nonempty ι] in
private theorem quotient_mean {w u v : ι → ℝ} (mass : ∑ i,w i=1)
    (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i) {P : ℝ} (hP : 0<P) :
    geometricMean w (fun i => P/(u i*v i))*geometricMean w u*geometricMean w v=P := by
  let y (i : ι) := P/(u i*v i)
  have h (i : ι) : 0<u i*v i := mul_pos (hu i) (hv i)
  have eq : (fun i => y i*(u i*v i))=(fun _ : ι => P) :=
    funext fun i => div_mul_cancel₀ P (h i).ne'
  have id := congrArg (geometricMean w) eq
  rw [geometricMean_mul w (fun i => div_pos hP (h i)) h,geometricMean_mul w hu hv,
    geometricMean_const mass hP] at id
  exact (mul_assoc ..).trans id

private theorem balance {μ m x P r : ℝ} (hm : 0<μ) (hx : 0<x) (hP : 0<P) :
    μ*x=m*x^r+P ↔ P/(μ*x)+(m/μ^r*P^(r-1))*(P/(μ*x))^(1-r)=1 := by
  have dp := mul_pos hm hx
  have price : (m/μ^r*P^(r-1))*(P/(μ*x))^(1-r)=m*x^r/(μ*x) := by
    rw [Real.rpow_sub hP,Real.rpow_one,Real.rpow_sub (div_pos hP dp),Real.rpow_one,
      Real.div_rpow hP.le dp.le,Real.mul_rpow hm.le hx.le]
    field_simp [hP.ne',hm.ne',hx.ne',(Real.rpow_pos_of_pos hP r).ne',
      (Real.rpow_pos_of_pos hm r).ne',(Real.rpow_pos_of_pos hx r).ne']
  rw [price,←add_div,div_eq_iff dp.ne',one_mul]
  constructor <;> intro h <;> linarith only [h]

/-- A larger common coupling, larger masses or smaller self-couplings
can only increase the synchronized densities, coordinate by coordinate. -/
theorem synchronized_comparison {w μ ν m n x y : ι → ℝ} {r b c : ℝ}
    (hw : ∀ i, 0≤w i) (mass : ∑ i,w i=1) (hm : ∀ i, 0 < m i) (hr : r<1) (hb : 0≤b)
    (hμ : ∀ i, ν i≤μ i) (hmn : ∀ i, m i≤n i) (hbc : b≤c)
    (fx : Synchronized w μ m r b x) (fy : Synchronized w ν n r c y) : ∀ i, x i≤y i := by
  classical
  obtain ⟨j,_,maximal⟩ := univ.exists_max_image (fun i => x i/y i) univ_nonempty
  let T := x j/y j
  have tp : 0<T := div_pos (fx.1 j) (fy.1 j)
  have cmp (i : ι) : x i≤T*y i := (div_le_iff₀ (fy.1 i)).mp (maximal i (mem_univ _))
  have atj : x j=T*y j := (div_mul_cancel₀ _ (fy.1 j).ne').symm
  suffices h : T≤1 by
    exact fun i => (cmp i).trans (mul_le_of_le_one_left (fy.1 i).le h)
  by_contra! big
  have power := Real.rpow_lt_rpow_of_exponent_lt big hr
  rw [Real.rpow_one] at power
  have jpow : (x j)^r<T*(y j)^r := by
    rw [atj,Real.mul_rpow tp.le (fy.1 j).le]
    exact mul_lt_mul_of_pos_right power (Real.rpow_pos_of_pos (fy.1 j) r)
  have mean := geometricMean_mono hw fx.1 cmp
  rw [geometricMean_mul w (fun _ => tp) fy.1,geometricMean_const mass tp] at mean
  have p := mul_lt_mul_of_pos_left jpow (hm j)
  have q := mul_le_mul_of_nonneg_right (hmn j) (mul_pos tp (Real.rpow_pos_of_pos (fy.1 j) r)).le
  have coupling := mul_le_mul_of_nonneg_left mean hb
  have gy : 0<geometricMean w y := Real.exp_pos _
  have stronger := mul_le_mul_of_nonneg_right hbc (mul_pos tp gy).le
  have self := mul_le_mul_of_nonneg_right (hμ j) (fx.1 j).le
  have own := fx.2 j
  have other := congrArg (fun z : ℝ => T*z) (fy.2 j)
  rw [atj] at own self
  rw [atj] at p
  linarith only [own,other,self,p,q,coupling,stronger]

theorem coupling_lt_geometric_mean {w μ m x : ι → ℝ} {r b : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (hμ : ∀ i, 0<μ i) (hm : ∀ i, 0 < m i)
    (hb : 0<b) (hx : Synchronized w μ m r b x) : b<geometricMean w μ := by
  have gx : 0<geometricMean w x := Real.exp_pos _
  have sites (i : ι) : b*geometricMean w x<μ i*x i := by
    rw [hx.2 i]
    exact lt_add_of_pos_left _ (mul_pos (hm i) (Real.rpow_pos_of_pos (hx.1 i) r))
  have strict := geometricMean_lt hw (fun _ => mul_pos hb gx) sites
  rw [geometricMean_const mass (mul_pos hb gx),geometricMean_mul w hμ hx.1] at strict
  exact lt_of_mul_lt_mul_right strict gx.le

/-- A strict mass increase at even one coordinate propagates through
the positive product coupling to every coordinate of the response. -/
theorem strict_response_to_one_mass {w μ m n x y : ι → ℝ} {r b : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (hm : ∀ i, 0 < m i) (hr : r<1) (hb : 0<b)
    (hmn : ∀ i, m i≤n i) (j : ι) (hj : m j<n j)
    (fx : Synchronized w μ m r b x) (fy : Synchronized w μ n r b y) : ∀ i, x i<y i := by
  have cmp := synchronized_comparison (fun i => (hw i).le) mass hm hr hb.le
    (fun _ => le_rfl) hmn le_rfl fx fy
  have all := geometricMean_mono (fun i => (hw i).le) fx.1 cmp
  have localGain : x j<y j := (cmp j).lt_of_ne fun eq => by
    have own := fx.2 j
    rw [eq] at own
    have diff := mul_lt_mul_of_pos_right hj (Real.rpow_pos_of_pos (fy.1 j) r)
    linarith only [own,fy.2 j,diff,mul_le_mul_of_nonneg_left all hb.le]
  have mean : geometricMean w x<geometricMean w y := by
    apply Real.exp_lt_exp.mpr
    apply sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (Real.log_le_log (fx.1 i) (cmp i)) (hw i).le)
    exact ⟨j,mem_univ j,mul_lt_mul_of_pos_left (Real.log_lt_log (fx.1 j) localGain) (hw j)⟩
  intro i
  apply (cmp i).lt_of_ne
  intro eq
  have own := fx.2 i
  rw [eq] at own
  linarith only [own,fy.2 i,mul_lt_mul_of_pos_left mean hb,
    mul_le_mul_of_nonneg_right (hmn i) (Real.rpow_pos_of_pos (fy.1 i) r).le]

/-- Existence and uniqueness for any finite family of positive masses,
self-couplings and normalized interaction weights. -/
theorem weighted_synchronization_iff {w μ m : ι → ℝ} {r b : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (hμ : ∀ i, 0<μ i) (hm : ∀ i, 0 < m i)
    (small : r<1) (hb : 0<b) :
    (∃! x, Synchronized w μ m r b x) ↔ b<geometricMean w μ := by
  constructor
  · exact fun ⟨_,hx,_⟩ => coupling_lt_geometric_mean hw mass hμ hm hb hx
  · intro threshold
    let a (i : ι) := m i/(μ i)^r
    have ap (i : ι) : 0<a i := div_pos (hm i) (Real.rpow_pos_of_pos (hμ i) r)
    have gp : 0<geometricMean w μ := Real.exp_pos _
    have rp := sub_pos.mpr small
    obtain ⟨t,⟨ht,share⟩,_⟩ := unique_prescribed_load hw mass ap rp (div_pos hb gp)
      ((div_lt_one gp).mpr threshold)
    let P := t^(1/(r-1))
    let v (i : ι) := fraction (1-r) (a i*t)
    let x (i : ι) := P/(μ i*v i)
    have pp : 0<P := Real.rpow_pos_of_pos ht _
    have vp (i : ι) : 0<v i := (fraction_spec rp (mul_pos (ap i) ht).le).1
    have xp (i : ι) : 0<x i := div_pos pp (mul_pos (hμ i) (vp i))
    have tpow : P^(r-1)=t := by
      dsimp only [P]
      rw [←Real.rpow_mul ht.le,show 1/(r-1)*(r-1)=1 by field_simp [sub_ne_zero.mpr small.ne],Real.rpow_one]
    have product := quotient_mean mass hμ vp pp
    change geometricMean w x*geometricMean w μ*geometricMean w v=P at product
    change geometricMean w v=b/geometricMean w μ at share
    rw [share] at product
    have pressure : b*geometricMean w x=P := by
      calc _ = geometricMean w x*geometricMean w μ*(b/geometricMean w μ) := by field_simp [gp.ne']
           _ = P := product
    have sol : Synchronized w μ m r b x := by
      refine ⟨xp,fun i => ?_⟩
      rw [pressure]
      apply (balance (hμ i) (xp i) pp).mpr
      have recover : P/(μ i*x i)=v i := by dsimp only [x]; field_simp [(hμ i).ne',(vp i).ne',pp.ne']
      rw [recover,tpow]
      exact (fraction_spec rp (mul_pos (ap i) ht).le).2.2
    have cmp {u v : ι → ℝ} (hu : Synchronized w μ m r b u) (hv : Synchronized w μ m r b v) :=
      synchronized_comparison (fun i => (hw i).le) mass hm small hb.le (fun _ => le_rfl) (fun _ => le_rfl) le_rfl hu hv
    exact ⟨x,sol,fun y hy => funext fun i => le_antisymm (cmp hy sol i) (cmp sol hy i)⟩

/-- Physical amplitude equations for a homogeneous interaction of
degree p. The mixed term is the product with individual exponents pwᵢ. -/
def Amplitudes (w μ m : ι → ℝ) (p b : ℝ) (u : ι → ℝ) : Prop :=
  (∀ i, 0<u i) ∧ ∀ i, μ i*(u i)^p=m i*(u i)^2+b*∏ j, (u j)^(p*w j)

omit [Nonempty ι] in
private theorem amplitude_density {w μ m u : ι → ℝ} {p b : ℝ} (hp : 0<p) (hu : ∀ i, 0<u i) :
    Amplitudes w μ m p b u ↔ Synchronized w μ m (2/p) b (fun i => (u i)^p) := by
  have square (i : ι) : ((u i)^p)^(2/p)=(u i)^2 := by
    rw [←Real.rpow_mul (hu i).le,show p*(2/p)=2 by field_simp [hp.ne'],Real.rpow_two]
  have product : geometricMean w (fun i => (u i)^p)=∏ j, (u j)^(p*w j) := by
    rw [geometricMean,Real.exp_sum]
    apply prod_congr rfl
    intro j _
    rw [Real.log_rpow (hu j),Real.rpow_def_of_pos (hu j)]
    congr 1
    ring
  simp only [Synchronized,Amplitudes,product,square,hu,fun i => Real.rpow_pos_of_pos (hu i) p,
    implies_true,true_and]

private theorem undo_power {x p : ℝ} (hx : 0<x) (hp : p≠0) :
    (x^p)^(1/p)=x := by rw [←Real.rpow_mul hx.le,show p*(1/p)=1 by field_simp [hp],Real.rpow_one]

/-- The geometric-mean threshold in the original amplitude variables
for any p>2. Taking p=2N/(N−2), wᵢ=1/K and mᵢ=1 gives the algebraic
system of Fan–Giaretto–Soave. At or above the threshold no state exists. -/
theorem physical_amplitude_threshold {w μ m : ι → ℝ} {p b : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (hμ : ∀ i, 0<μ i) (hm : ∀ i, 0 < m i)
    (hp : 2<p) (hb : 0<b) :
    ((∃! u, Amplitudes w μ m p b u) ↔ b<geometricMean w μ) ∧
      (geometricMean w μ≤b → ¬ ∃ u, Amplitudes w μ m p b u) := by
  have pp : 0<p := (by norm_num : (0:ℝ)<2).trans hp
  have necessary {u} (hu : Amplitudes w μ m p b u) :=
    coupling_lt_geometric_mean hw mass hμ hm hb ((amplitude_density pp hu.1).mp hu)
  refine ⟨⟨fun ⟨_,hu,_⟩ => necessary hu,?_⟩,fun high ⟨_,hu⟩ => (necessary hu).not_ge high⟩
  intro below
  obtain ⟨y,hy,only⟩ := (weighted_synchronization_iff hw mass hμ hm ((div_lt_one pp).mpr hp) hb).mpr below
  let u (i : ι) := (y i)^(1/p)
  have up (i : ι) : 0<u i := Real.rpow_pos_of_pos (hy.1 i) _
  have gain (i : ι) : (u i)^p=y i := by
    dsimp only [u]
    rw [←Real.rpow_mul (hy.1 i).le,show 1/p*p=1 by field_simp [pp.ne'],Real.rpow_one]
  have sol : Amplitudes w μ m p b u := by
    apply (amplitude_density pp up).mpr
    simpa only [gain] using hy
  refine ⟨u,sol,fun z hz => funext fun i => ?_⟩
  have eq := congrFun (only _ ((amplitude_density pp hz.1).mp hz)) i
  calc z i = ((z i)^p)^(1/p) := (undo_power (hz.1 i) pp.ne').symm
       _ = u i := congrArg (fun t : ℝ => t^(1/p)) eq

#print axioms strict_response_to_one_mass
#print axioms physical_amplitude_threshold
#print axioms weighted_synchronization_iff
#print axioms synchronized_comparison
end HTGeometry.WeightedCriticalModes
