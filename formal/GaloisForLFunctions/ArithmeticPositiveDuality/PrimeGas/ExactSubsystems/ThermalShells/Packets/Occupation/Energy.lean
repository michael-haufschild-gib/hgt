import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Limit

/-! # The centered many-prime Hamiltonian and its limiting energy levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset Filter Topology Real Set _root_.RHTower
open BinaryOrientation.LargestPrime.Bands
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
local instance : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective

def radius (k : ℝ) (m : ℕ) (t : ℝ) :=
  (m:ℝ)*max (log (1+1/t)) (log (1+k/t))

theorem radius_limit (k : ℝ) (m : ℕ) : Tendsto (radius k m) atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => (m:ℝ)*max (log (1+1/t)) (log (1+k/t))) atTop (𝓝 0)
  simpa only [max_self,mul_zero] using ((logWidth_limit 1).max (logWidth_limit k)).const_mul (m:ℝ)

/-- Every configuration with j upper occupations has centered energy within one packet-width
per occupied mode of the lattice energy jD. -/
theorem energy_local {S : Finset Nat.Primes} {D k t : ℝ} (hk : 0 < k) (ht : 0 < t) {m : ℕ}
    {R : BreadthSubset m ↥S} (hr : R ∈ sector S (both D k t) m) :
    |(energyOf R-(m:ℝ)*t)-(upperCount (modes S (high D k t)) R:ℝ)*D| ≤ radius k m t := by
  let H := modes S (high D k t)
  let w := max (log (1+1/t)) (log (1+k/t))
  let e (p : ↥S) := squarefreePrimeEnergy p.val-t-(if p ∈ H then D else 0)
  have each p (hp : p ∈ R.val) : |e p| ≤ w := by
    have hn : serial p ∈ both D k t := (mem_filter.mp ((mem_filter.mp hr).2 hp)).2
    by_cases hh : serial p ∈ high D k t
    · have hm : p ∈ H := mem_filter.mpr ⟨mem_univ _,hh⟩
      obtain ⟨_,hl,hu⟩ := high_energy hk ht hh
      change t+(D-log (1+k/t)) < squarefreePrimeEnergy p.val at hl
      change squarefreePrimeEnergy p.val ≤ t+D at hu
      rw [e,if_pos hm,abs_le]
      have hw : 0 ≤ log (1+k/t) := log_nonneg (by linarith only [div_pos hk ht])
      constructor <;> linarith only [hl,hu,hw,(le_max_right (log (1+1/t)) (log (1+k/t)) : _ ≤ w)]
    · have hm : p ∉ H := fun h => hh (mem_filter.mp h).2
      obtain ⟨_,hl,hu⟩ := low_energy ht ((mem_union.mp hn).resolve_right hh)
      change t < squarefreePrimeEnergy p.val at hl
      change squarefreePrimeEnergy p.val ≤ t+log (1+1/t) at hu
      rw [e,if_neg hm,sub_zero,abs_of_nonneg (sub_nonneg.mpr hl.le)]
      exact (by linarith only [hu,(le_max_left (log (1+1/t)) (log (1+k/t)) : _ ≤ w)])
  have q : (∑ p ∈ R.val, if p ∈ H then D else 0) = (upperCount H R:ℝ)*D := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]; rfl
  have total : (∑ p ∈ R.val,e p) = (energyOf R-(m:ℝ)*t)-(upperCount H R:ℝ)*D := by
    simp only [e,sum_sub_distrib,sum_const,nsmul_eq_mul,R.property,q,energyOf]
  rw [← total]
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum each).trans_eq (by simp only [sum_const,nsmul_eq_mul,R.property,radius,w]))

/-- Conditional expectation over a finite selection. -/
def average {α : Type*} (w : α → ℝ) (U : Finset α) (f : α → ℝ) := (∑ x ∈ U, w x*f x)/mass w U

private theorem avg_diff {α : Type*} (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (U : Finset α)
    (f g : α → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ x ∈ U, |f x-g x| ≤ ε) :
    |average w U f-average w U g| ≤ ε := by
  have hd : 0 ≤ mass w U := sum_nonneg fun x _ => hw x
  by_cases h : mass w U = 0
  · simpa only [average,h,div_zero,sub_self,abs_zero] using hε
  have eqv : (∑ x ∈ U, w x*f x)-(∑ x ∈ U, w x*g x) = ∑ x ∈ U, w x*(f x-g x) := by simp only [mul_sub,sum_sub_distrib]
  rw [average,average,← sub_div,eqv,abs_div,abs_of_nonneg hd,div_le_iff₀ (lt_of_le_of_ne hd (Ne.symm h))]
  calc _ ≤ ∑ x ∈ U, |w x*(f x-g x)| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ x ∈ U, w x*ε := sum_le_sum fun x hx => by rw [abs_mul,abs_of_nonneg (hw x)]; exact mul_le_mul_of_nonneg_left (he x hx) (hw x)
       _ = _ := by rw [← sum_mul,mul_comm]; rfl

private theorem born_pos {S : Finset Nat.Primes} {m : ℕ} (b : ℝ) (R : BreadthSubset m ↥S) : 0 < born b R := by
  rw [born,finiteSquarefreeBornWeight_eq]
  exact div_pos (exp_pos _) (finiteSquarefreePartition_pos _ _)

def energyRead (c d D k b : ℝ) (m : ℕ) (f : ℝ → ℝ) (h : Ioi (0:ℝ)) :=
  let t := c/h.val
  average (born b) (sector (added c d h) (both D k t) m) fun R => f (energyOf R-(m:ℝ)*t)

private theorem lattice_read {S : Finset Nat.Primes} (P Q : Finset ℕ) (b D : ℝ) (m : ℕ) (f : ℝ → ℝ) :
    average (born b) (sector S P m) (fun R => f ((upperCount (modes S Q) R:ℝ)*D)) =
      ∑ j ∈ range (m+1), countRead S P Q b m {j}*f ((j:ℝ)*D) := by
  let U := sector S P m
  let J (R : BreadthSubset m ↥S) := upperCount (modes S Q) R
  have hJ (R : BreadthSubset m ↥S) : J R ≤ m := (card_filter_le _ _).trans_eq R.property
  let g (R : BreadthSubset m ↥S) := born b R*f ((J R:ℝ)*D)
  have fiber := sum_fiberwise_of_maps_to (s := U) (t := range (m+1)) (g := J)
    (fun R _ => mem_range.mpr (Nat.lt_succ_of_le (hJ R))) g
  change (∑ R ∈ U, g R)/mass (born b) U = _
  rw [← fiber,sum_div]
  apply sum_congr rfl
  intro j _
  change (∑ R ∈ U.filter (fun R => J R=j), g R)/_ = share _ U (U.filter (fun R => J R ∈ ({j}:Finset ℕ)))*_
  simp only [mem_singleton,share,mass]
  rw [div_mul_eq_mul_div₀,Finset.sum_mul]
  congr 1
  apply sum_congr rfl
  intro R hr
  simp only [g,(mem_filter.mp hr).2]

/-- The centered Hamiltonian converges against every continuous test to the binomial
mixture of the lattice levels 0,D,...,mD. -/
theorem energy_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (energyRead c d D k b m f) criticalApproach
      (𝓝 (∑ j ∈ range (m+1), bin m j (upperProbability D k b)*f ((j:ℝ)*D))) := by
  let lattice (h : Ioi (0:ℝ)) := ∑ j ∈ range (m+1), read c d D k b m {j} h*f ((j:ℝ)*D)
  have lim : Tendsto lattice criticalApproach _ := tendsto_finsetSum _ fun j _ => (cell_limit hc hcd hD hk b m j).mul_const _
  have rad := (radius_limit k m).comp (translation_limit hc)
  have err : Tendsto (fun h => energyRead c d D k b m f h-lattice h) criticalApproach (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have localBound (j : ℕ) : ∀ᶠ h : Ioi (0:ℝ) in criticalApproach, ∀ x : ℝ,
        |x-(j:ℝ)*D| ≤ radius k m (c/h.val) → |f x-f ((j:ℝ)*D)| ≤ ε/2 := by
      obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := (j:ℝ)*D)) (ε/2) (half_pos hε)
      filter_upwards [rad.eventually_lt_const hδ] with h hr
      intro x hx
      exact (hd ((Real.dist_eq _ _).symm ▸ hx.trans_lt hr)).le
    filter_upwards [(Filter.eventually_all_finset (range (m+1))).mpr (fun j _ => localBound j)] with h hh
    let t := c/h.val
    let S := added c d h
    let U := sector S (both D k t) m
    let J (R : BreadthSubset m ↥S) := upperCount (modes S (high D k t)) R
    have hl : average (born b) U (fun R => f ((J R:ℝ)*D)) = lattice h := lattice_read _ _ _ _ _ _
    rw [Real.dist_eq,sub_zero,← hl]
    exact (avg_diff (born b) (fun R => (born_pos b R).le) U _ _ (half_pos hε).le (fun R hr =>
      hh (J R) (mem_range.mpr (Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq R.property)))
        _ (energy_local hk (div_pos hc h.property) hr))).trans_lt (half_lt_self hε)
  have sum := err.add lim
  rw [zero_add] at sum
  exact sum.congr fun h => sub_add_cancel _ _

#print axioms energy_local
#print axioms energy_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
