import GaloisForLFunctions.MultiplicativePositivityGeometry.TheEquilibriumOfTheThreeSitePrimeGram

/-!
# Spreading prime Gram mass on two logarithmic steps

In the energy-splitting argument of Carrillo, Guimarães, Padilla-Garza
and Shu (Lemma 25), inserting a site depends on its potential. Equal
masses on a rectangular grid of two incommensurable prime logarithms
make the potential uniformly small at every translate. Consequently
each finite prime Gram configuration admits strict improvements arbitrarily
far out, and the infimum over finite probability distributions is zero.
-/
noncomputable section
open Finset Complex Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.MultiplicativePositivityGeometry

private abbrev clock := _root_.HTGeometry.phaseClockValue

private theorem clock_norm (r t : ℝ) : ‖clock r t‖ = 1 := by
  simp [clock,_root_.HTGeometry.phaseClockValue,Complex.norm_exp]

private theorem clock_add (r s t : ℝ) : clock r (s+t) = clock r s*clock r t := by
  unfold clock _root_.HTGeometry.phaseClockValue
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem clock_mul_nat (r t : ℝ) (k : ℕ) : clock r (k*t) = (clock t r)^k := by
  unfold clock _root_.HTGeometry.phaseClockValue
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- Equal grid weights at displacements i log p + j log q. -/
def primeGridMean (p q N : ℕ) (f : ℝ → ℝ) (u : ℝ) :=
  (N:ℝ)⁻¹ * ((N:ℝ)⁻¹ * ∑ i ∈ range N, ∑ j ∈ range N,
    f (u+i*Real.log p+j*Real.log q))

private def multiplier (p q N : ℕ) (r : ℝ) :=
  cesaro N (clock (Real.log p) r) * cesaro N (clock (Real.log q) r)

private theorem multiplier_norm (p q N : ℕ) (r : ℝ) : ‖multiplier p q N r‖ ≤ 1 := by
  rw [multiplier,norm_mul]
  exact (mul_le_mul (norm_cesaro_le (clock_norm _ _).le _) (norm_cesaro_le (clock_norm _ _).le _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem multiplier_limit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p ≠ q)
    {r : ℝ} (hr : r ≠ 0) : Tendsto (fun N => multiplier p q N r) atTop (𝓝 0) := by
  have sep : ¬(clock (Real.log p) r=1 ∧ clock (Real.log q) r=1) := by
    rintro ⟨a,b⟩
    apply hr
    apply _root_.RHTower.primeLogPhaseClockPair_injective hp hq ne
    apply Prod.ext <;> simp only [_root_.RHTower.primeLogPhaseClockPair,_root_.HTGeometry.phaseClockPair]
    · simpa only [clock,_root_.HTGeometry.phaseClockValue,mul_zero,ofReal_zero,zero_mul,exp_zero] using a
    · simpa only [clock,_root_.HTGeometry.phaseClockValue,mul_zero,ofReal_zero,zero_mul,exp_zero] using b
  have h := (tendsto_cesaro (clock_norm (Real.log p) r).le).mul (tendsto_cesaro (clock_norm (Real.log q) r).le)
  by_cases h₁ : clock (Real.log p) r = 1
  · simpa only [multiplier,if_pos h₁,if_neg (fun h₂ => sep ⟨h₁,h₂⟩),mul_zero] using h
  · simpa only [multiplier,if_neg h₁,zero_mul] using h

private theorem grid_cos (p q N : ℕ) (r u : ℝ) :
    primeGridMean p q N (fun t => Real.cos (r*t)) u = (clock r u*multiplier p q N r).re := by
  have eq : clock r u * multiplier p q N r =
      (((N:ℝ)⁻¹:ℝ):ℂ) * ((((N:ℝ)⁻¹:ℝ):ℂ) * ∑ i ∈ range N, ∑ j ∈ range N,
          clock r (u+i*Real.log p+j*Real.log q)) := by
    simp only [clock_add,clock_mul_nat,←Finset.mul_sum,←Finset.sum_mul,multiplier,cesaro,
      Complex.ofReal_inv,Complex.ofReal_natCast]
    ring
  rw [eq]
  simp only [primeGridMean,Complex.re_sum,Complex.ofReal_mul_re,clock,_root_.HTGeometry.phaseClockValue,
    Complex.exp_ofReal_mul_I_re]

private def blur (p q N : ℕ) (h : ℝ) :=
  ∑' n, zetaBoundaryWeight h n * ‖multiplier p q N (Real.log n)‖

private theorem blur_limit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p ≠ q)
    {h : ℝ} (hh : 0 < h) : Tendsto (fun N => blur p q N h) atTop (𝓝 0) := by
  have point (n : ℕ) : Tendsto (fun N => zetaBoundaryWeight h n*‖multiplier p q N (Real.log n)‖)
      atTop (𝓝 0) := by
    rcases le_or_gt n 1 with small|large
    · have e : n=0 ∨ n=1 := by omega
      rcases e with rfl|rfl <;> simp [zetaBoundaryWeight]
    · have hn := Real.log_pos (by exact_mod_cast large : (1:ℝ) < n)
      simpa only [norm_zero,mul_zero] using
        (multiplier_limit hp hq ne hn.ne').norm.const_mul (zetaBoundaryWeight h n)
  have bound (N n : ℕ) : ‖zetaBoundaryWeight h n*‖multiplier p q N (Real.log n)‖‖ ≤ zetaBoundaryWeight h n := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (zetaBoundaryWeight_nonneg _ _) (norm_nonneg _))]
    exact mul_le_of_le_one_right (zetaBoundaryWeight_nonneg _ _) (multiplier_norm ..)
  simpa only [blur,tsum_zero] using tendsto_tsum_of_dominated_convergence
    (bound:=zetaBoundaryWeight h) (summable_zetaBoundaryWeight hh) point (Eventually.of_forall bound)

private theorem grid_price (p q N : ℕ) {h : ℝ} (hh : 0 < h) (u : ℝ) :
    |primeGridMean p q N (zetaRealLogDeriv (1+h)) u| ≤ blur p q N h := by
  let w := zetaBoundaryWeight h
  let f := fun (n : ℕ) (v : ℝ) => w n*Real.cos (Real.log n*v)
  have hs (v : ℝ) : HasSum (fun n => f n v) (zetaRealLogDeriv (1+h) v) := by
    rw [zetaRealLogDeriv_eq_cosineTrace hh]
    exact (summable_cosineTrace_terms (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh)
      logFrequency v).hasSum
  have sum := ((hasSum_sum (s:=range N) fun i _ => hasSum_sum (s:=range N) fun j _ =>
    hs (u+i*Real.log p+j*Real.log q)).mul_left ((N:ℝ)⁻¹)).mul_left ((N:ℝ)⁻¹)
  change HasSum (fun n => primeGridMean p q N (f n) u) (primeGridMean p q N (zetaRealLogDeriv (1+h)) u) at sum
  have term (n : ℕ) : |primeGridMean p q N (f n) u| ≤ w n*‖multiplier p q N (Real.log n)‖ := by
    have linear : primeGridMean p q N (f n) u = w n*primeGridMean p q N (fun t => Real.cos (Real.log n*t)) u := by
      simp only [primeGridMean,f,←mul_sum];ring
    rw [linear,abs_mul,abs_of_nonneg (zetaBoundaryWeight_nonneg _ _),grid_cos]
    apply mul_le_mul_of_nonneg_left _ (zetaBoundaryWeight_nonneg _ _)
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul,clock_norm,one_mul])
  have hblur : Summable fun n => w n*‖multiplier p q N (Real.log n)‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (zetaBoundaryWeight_nonneg _ _) (norm_nonneg _))
      (fun n => mul_le_of_le_one_right (zetaBoundaryWeight_nonneg _ _) (multiplier_norm ..)) (summable_zetaBoundaryWeight hh)
  rw [← sum.tsum_eq,← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm sum.summable.norm).trans
  exact sum.summable.norm.tsum_le_tsum (fun n => by simpa only [Real.norm_eq_abs] using term n) hblur

/-- The potentials of the equal grid measures on any two distinct prime
logarithms tend uniformly to zero on the entire real line. -/
theorem two_prime_grid_potential_vanishes_uniformly {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ne : p ≠ q) {h ε : ℝ} (hh : 0<h) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, |primeGridMean p q N (zetaRealLogDeriv (1+h)) u| < ε := by
  filter_upwards [(blur_limit hp hq ne hh).eventually_lt_const he] with N hb
  exact fun u => (grid_price p q N hh u).trans_lt hb

private theorem grid_const (p q : ℕ) {N : ℕ} (hN : 0 < N) (u a : ℝ) :
    primeGridMean p q N (fun _ => a) u = a := by
  simp only [primeGridMean,sum_const,card_range,nsmul_eq_mul]
  field_simp [(Nat.cast_pos.mpr hN : 0 < (N:ℝ)).ne']

private theorem grid_mono (p q N : ℕ) (u : ℝ) {f g : ℝ → ℝ}
    (le : ∀ i ∈ range N, ∀ j ∈ range N,
      f (u+i*Real.log p+j*Real.log q) ≤ g (u+i*Real.log p+j*Real.log q)) :
    primeGridMean p q N f u ≤ primeGridMean p q N g u := by
  have pos := inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) N)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_le_sum fun i hi =>
    sum_le_sum fun j hj => le i hi j hj) pos) pos

/-- Self-energy of the uniform probability weights on all N² grid sites. -/
def primeGridEnergy (p q N : ℕ) (h : ℝ) :=
  primeGridMean p q N (fun t => primeGridMean p q N (zetaRealLogDeriv (1+h)) (-t)) 0

/-- Explicit finite prime Gram measures whose self-energy tends to zero. -/
theorem prime_grid_energy_tends_to_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ne : p ≠ q) {h : ℝ} (hh : 0<h) : Tendsto (fun N => primeGridEnergy p q N h) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [two_prime_grid_potential_vanishes_uniformly hp hq ne hh (half_pos he),
    eventually_ge_atTop 1] with N small hn
  let f := fun u => primeGridMean p q N (zetaRealLogDeriv (1+h)) (-u)
  have low := grid_mono p q N 0 (f:=fun _ => -(ε/2)) (g:=f)
    (fun i _ j _ => ((abs_lt.mp (small _)).1).le)
  have up := grid_mono p q N 0 (f:=f) (g:=fun _ => ε/2)
    (fun i _ j _ => ((abs_lt.mp (small _)).2).le)
  rw [grid_const p q hn] at low up
  rw [Real.dist_eq,sub_zero]
  exact ((abs_le.mpr ⟨low,up⟩).trans_lt (half_lt_self he))

/-- Potential of a finite distribution of masses at the observation u. -/
def sitePotential {m : ℕ} (h : ℝ) (x a : Fin m → ℝ) (u : ℝ) :=
  ∑ i, a i*zetaRealLogDeriv (1+h) (u-x i)

private theorem potential_mean {m : ℕ} (h u : ℝ) (x a : Fin m → ℝ) (p q N : ℕ) :
    primeGridMean p q N (sitePotential h x a) u =
      ∑ i, a i*primeGridMean p q N (zetaRealLogDeriv (1+h)) (u-x i) := by
  unfold primeGridMean sitePotential
  rw [sum_congr rfl (fun i _ => sum_comm (s:=range N) (t:=univ)),sum_comm]
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro k _
  simp_rw [show ∀ i j : ℕ, u+i*Real.log p+j*Real.log q-x k = u-x k+i*Real.log p+j*Real.log q by intros;ring]
  simp only [←mul_sum];ring

/-- For every finite probability distribution there are arbitrarily late
sites with potential smaller than any prescribed positive level. -/
theorem distant_site_below_every_positive_level {m : ℕ} (x a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (unit : ∑ i, a i = 1) {h ε : ℝ} (hh : 0 < h) (he : 0 < ε) (A : ℝ) :
    ∃ u ≥ A, sitePotential h x a u < ε := by
  obtain ⟨N,small,hn⟩ := ((two_prime_grid_potential_vanishes_uniformly (by decide : Nat.Prime 2)
    (by decide : Nat.Prime 3) (by decide) hh (half_pos he)).and (eventually_ge_atTop 1)).exists
  by_contra! lower
  have onGrid := grid_mono 2 3 N A (f:=fun _ => ε) (g:=sitePotential h x a) (fun i _ j _ =>
    lower _ (by have h₂ := mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) (Real.log_natCast_nonneg 2)
                have h₃ := mul_nonneg (Nat.cast_nonneg (α:=ℝ) j) (Real.log_natCast_nonneg 3)
                linarith only [h₂,h₃]))
  rw [grid_const _ _ hn,potential_mean] at onGrid
  have cap := sum_le_sum (s:=univ) (fun i _ => mul_le_mul_of_nonneg_left
    ((abs_lt.mp (small (A-x i))).2.le) (ha i))
  rw [←sum_mul,unit,one_mul] at cap
  exact (half_lt_self he).not_ge (onGrid.trans cap)

/-- Prime Gram energy of masses at the given heights. -/
def siteEnergy {m : ℕ} (h : ℝ) (x a : Fin m → ℝ) :=
  ∑ i, a i * sitePotential h x a (x i)

private theorem insert_energy {m : ℕ} (x a : Fin m → ℝ) {h : ℝ} (hh : 0 < h)
    (u t : ℝ) :
    siteEnergy h (Fin.cons u x) (Fin.cons t (fun i => (1-t)*a i)) =
      (1-t)^2*siteEnergy h x a + 2*t*(1-t)*sitePotential h x a u +
        t^2*zetaRealLogDeriv (1+h) 0 := by
  let f := zetaRealLogDeriv (1+h)
  have sym (v : ℝ) : f (v-u) = f (u-v) := by
    rw [show v-u= -(u-v) by ring]
    simp only [f,zetaRealLogDeriv_eq_cosineTrace hh,cosineTrace_neg]
  have row (v : ℝ) : sitePotential h (Fin.cons u x) (Fin.cons t (fun i => (1-t)*a i)) v =
      t*f (v-u)+(1-t)*sitePotential h x a v := by
    unfold sitePotential
    rw [Fin.sum_univ_succ,mul_sum]
    simp only [Fin.cons_zero,Fin.cons_succ]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  have rest : (∑ i, (1-t)*a i*(t*f (x i-u)+(1-t)*sitePotential h x a (x i))) =
      t*(1-t)*sitePotential h x a u + (1-t)^2*siteEnergy h x a := by
    change _ = t*(1-t)*(∑ i, a i*f (u-x i)) + (1-t)^2*(∑ i, a i*sitePotential h x a (x i))
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [sym]
    ring
  change (∑ i, (Fin.cons t (fun i => (1-t)*a i)) i *
    sitePotential h (Fin.cons u x) (Fin.cons t (fun i => (1-t)*a i)) ((Fin.cons u x) i)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,row,sub_self,rest]
  dsimp only [f];ring

/-- Adding one arbitrarily late site strictly improves every finite
probability configuration on distinct sites. If its energy is E and
the diagonal is B, the improvement exceeds E²/(4(E+B)). -/
theorem adding_a_distant_site_improves_energy {m : ℕ} (x a : Fin m → ℝ)
    (distinct : Function.Injective x) (ha : ∀ i, 0 ≤ a i) (unit : ∑ i, a i = 1)
    {h : ℝ} (hh : 0<h) (A : ℝ) :
    let E := siteEnergy h x a
    let B := zetaRealLogDeriv (1+h) 0
    ∃ u ≥ A, (∀ i, x i < u) ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      siteEnergy h (Fin.cons u x) (Fin.cons t (fun i => (1-t)*a i)) <
        E-E^2/(4*(E+B)) := by
  intro E B
  have nonzero : a ≠ 0 := by rintro rfl; simp at unit
  have strict := zeta_gram_strict distinct nonzero hh
  have ep : 0 < E := by
    dsimp only [E,siteEnergy,sitePotential]
    simp only [mul_sum,←mul_assoc]
    exact strict
  have pos : 0 ≤ B := by
    rw [show B = cosineTrace (zetaBoundaryWeight h) logFrequency 0 from zetaRealLogDeriv_eq_cosineTrace hh 0]
    simp only [cosineTrace,mul_zero,Real.cos_zero,mul_one]
    exact tsum_nonneg (zetaBoundaryWeight_nonneg h)
  let U := max A (1+∑ i, |x i|)
  obtain ⟨u,hu,low⟩ := distant_site_below_every_positive_level x a ha unit hh (half_pos ep) U
  have beyond (i : Fin m) : x i < u := by
    have bound := (le_abs_self (x i)).trans (single_le_sum (fun j _ => abs_nonneg (x j)) (mem_univ i))
    exact (bound.trans_lt ((by linarith : (∑ j, |x j|) < 1+∑ j, |x j|))).trans_le ((le_max_right ..).trans hu)
  let t := E/(2*(E+B))
  have eb := add_pos_of_pos_of_nonneg ep pos
  have dp : 0 < 2*(E+B) := mul_pos (by norm_num) eb
  have tp : 0 < t := div_pos ep dp
  have small : t < 1 := (div_lt_one dp).mpr (by linarith only [ep,pos])
  have identity : t*(2*(E+B))=E := div_mul_cancel₀ _ dp.ne'
  have price : t*B ≤ E/2 := by nlinarith only [identity,mul_nonneg tp.le ep.le]
  refine ⟨u,(le_max_left ..).trans hu,beyond,t,tp,small,?_⟩
  rw [insert_energy x a hh]
  have mixed := mul_lt_mul_of_pos_left low (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) tp) (sub_pos.mpr small))
  have second := mul_le_mul_of_nonneg_left price tp.le
  have saving : E^2/(4*(E+B)) = t*E/2 := by dsimp only [t]; field_simp [eb.ne']; ring
  rw [saving]
  change (1-t)^2*E+2*t*(1-t)*sitePotential h x a u+t^2*B < _
  nlinarith only [mixed,second]



end GaloisForLFunctions.MultiplicativePositivityGeometry
