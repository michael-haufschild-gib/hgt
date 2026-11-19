import GaloisForLFunctions.SignedArithmeticCorrespondences.IndependentEnergiesOfInfiniteEndpointSections
import GaloisForLFunctions.SignedArithmeticCorrespondences.TheIntegralRangeOfTheMixedQuotientCells
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.RHTower.ConstrainedProlateRayleighFloor
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Absolute multiplicative incidence on infinite conductor supports

Cauchy–Schwarz along each increasing sequence of multiples bounds the
entire double series before forming quotient differences. Dominated
convergence then permits both supports to exhaust independently.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology

/-- Square norm of a conductor sequence extended by zero at unused indices. -/
def infiniteConductorNorm (f : ℕ → ℝ) : ℝ := Real.sqrt (∑' i, f i^2)

private theorem infinite_weighted_row (r w v : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hW : Summable (fun k => (w k/r k)^2)) (hV : Summable (fun j => (r j*v j)^2))
    (g : ℕ → ℕ) (hg : Function.Injective g) (hle : ∀ k, k≤g k) :
    Summable (fun k => w k* |v (g k)|) ∧
      ∑' k, w k* |v (g k)| ≤ infiniteConductorNorm (fun k => w k/r k)*
        infiniteConductorNorm (fun j => r j*v j) := by
  let p := fun k => w k/r k
  let z := fun j => r j* |v j|
  have hz (j : ℕ) : z j^2=(r j*v j)^2 := by simp only [z,mul_pow,sq_abs]
  have hZ : Summable (fun j => z j^2) := hV.congr fun j => (hz j).symm
  have hsub : Summable (fun k => z (g k)^2) := hZ.comp_injective hg
  have hprod := _root_.RHTower.summable_mul_of_sq_summable (f := p) (g := fun k => z (g k)) hW hsub
  have hc (k : ℕ) : w k* |v (g k)| ≤ p k*z (g k) := by
    calc _ = p k*(r k* |v (g k)|) := by dsimp only [p]; field_simp [(hr k).ne']
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (hm (hle k)) (abs_nonneg _)) (div_nonneg (hw _) (hr _).le)
  have hsum := Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (abs_nonneg _)) hc hprod
  refine ⟨hsum,(hsum.tsum_le_tsum hc hprod).trans ?_⟩
  apply (_root_.RHTower.tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq p (fun k => z (g k)) hW hsub
    (fun k => div_nonneg (hw k) (hr k).le) (fun k => mul_nonneg (hr _).le (abs_nonneg _))).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (tsum_comp_le_tsum_of_inj hZ (fun j => sq_nonneg _) hg).trans_eq (tsum_congr hz)

/-- Entrywise absolute cost at quotient k+1 and lower conductor i+1.
Shifting that quotient by one accounts for the second tail of each cell. -/
def conductorIncidence (s : ℕ) (w u v : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  |u (p.1+1)| * (w (p.2+1)* |v ((p.2+1+s)*(p.1+1))|)

/-- Every weighted arithmetic incidence is absolutely summable. Its total
cost is bounded by four separate scalar square norms. -/
theorem infinite_conductor_incidences (s : ℕ) (r w u v : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (w k/r k)^2))
    (hu : Summable (fun i => (r i*u i)^2)) (hv : Summable (fun i => (r i*v i)^2)) :
    Summable (conductorIncidence s w u v) ∧
      (∑' p, conductorIncidence s w u v p) ≤
        infiniteConductorNorm (fun k => 1/r k)*infiniteConductorNorm (fun k => w k/r k)*
          infiniteConductorNorm (fun i => r i*u i)*infiniteConductorNorm (fun i => r i*v i) := by
  let A := infiniteConductorNorm (fun k => 1/r k)
  let B := infiniteConductorNorm (fun k => w k/r k)
  let U := infiniteConductorNorm (fun i => r i*u i)
  let V := infiniteConductorNorm (fun i => r i*v i)
  have hrow (i : ℕ) :
      Summable (fun k => w (k+1)* |v ((k+1+s)*(i+1))|) ∧
      (∑' k, w (k+1)* |v ((k+1+s)*(i+1))|) ≤ B*V := by
    let g := fun k => (k+s)*(i+1)
    obtain ⟨hst,hcost⟩ := infinite_weighted_row r w v hr hm hw hB hv g
      (fun k j h => Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos i) h))
      (fun k => (Nat.le_add_right k s).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos i)))
    have hj : Function.Injective (fun k : ℕ => k+1) := fun _ _ h => Nat.add_right_cancel h
    exact ⟨hst.comp_injective hj,
      (tsum_comp_le_tsum_of_inj hst (fun k => mul_nonneg (hw k) (abs_nonneg _)) hj).trans hcost⟩
  have hu' := infinite_weighted_row r (fun _ => 1) u hr hm (fun _ => zero_le_one) hA hu
    (fun i => i+1) (fun _ _ h => Nat.add_right_cancel h) (fun i => Nat.le_succ i)
  simp only [one_mul] at hu'
  have hpos (p : ℕ × ℕ) : 0≤conductorIncidence s w u v p :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (hw _) (abs_nonneg _))
  have hcost (i : ℕ) : (∑' k, conductorIncidence s w u v (i,k)) ≤ |u (i+1)| * (B*V) := by
    simp only [conductorIncidence,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hrow i).2 (abs_nonneg _)
  have hmajor := hu'.1.mul_right (B*V)
  have hs := Summable.of_nonneg_of_le (fun i => tsum_nonneg fun k => hpos (i,k)) hcost hmajor
  have htotal : Summable (conductorIncidence s w u v) := (summable_prod_of_nonneg hpos).mpr
    ⟨fun i => (hrow i).1.mul_left |u (i+1)|,hs⟩
  refine ⟨htotal,?_⟩
  rw [htotal.tsum_prod]
  calc _ ≤ _ := hs.tsum_le_tsum hcost hmajor
       _ = (∑' i, |u (i+1)|)*(B*V) := by rw [tsum_mul_right]
       _ ≤ (A*U)*(B*V) := mul_le_mul_of_nonneg_right hu'.2 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
       _ = _ := by ring

/-- Absolute convergence of rounded bilinear entries under any summable
nonnegative entry price. The majorant is twice the limiting absolute entry. -/
private theorem pair_price_exhaustion {ι : Type*} (i j : ι → ℕ) (w : ι → ℝ) (u v : ℕ → ℝ)
    (hw : ∀ p, 0≤w p) (h : Summable (fun p => w p* |u (i p)*v (j p)|))
    (U V : ℕ → ℕ → ℝ) (hu : ∀ n, Tendsto (fun N => U N n) atTop (𝓝 (u n)))
    (hv : ∀ n, Tendsto (fun N => V N n) atTop (𝓝 (v n)))
    (hU : ∀ N n, |U N n| ≤ |u n|) (hV : ∀ N n, |V N n| ≤ |v n|) :
    Tendsto (fun N => ∑' p, w p* |U N (i p)*V N (j p)-u (i p)*v (j p)|) atTop (𝓝 0) := by
  let E (N : ℕ) (p : ι) := w p* |U N (i p)*V N (j p)-u (i p)*v (j p)|
  have he (p : ι) : Tendsto (fun N => E N p) atTop (𝓝 0) := by
    simpa only [E,sub_self,abs_zero,mul_zero] using
      ((((hu (i p)).mul (hv (j p))).sub_const (u (i p)*v (j p))).abs.const_mul (w p))
  have hb (N : ℕ) (p : ι) : ‖E N p‖ ≤ 2*(w p* |u (i p)*v (j p)|) := by
    have hm : |U N (i p)*V N (j p)| ≤ |u (i p)*v (j p)| := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (hU N _) (hV N _) (abs_nonneg _) (abs_nonneg _)
    change ‖w p* |U N (i p)*V N (j p)-u (i p)*v (j p)|‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw _) (abs_nonneg _))]
    calc _ ≤ w p*(|u (i p)*v (j p)|+|u (i p)*v (j p)|) :=
            mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hm le_rfl)) (hw _)
         _ = _ := by ring
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence (h.mul_left 2) he (Eventually.of_forall hb))

/-- Pointwise exhaustion dominated by the two limiting divisors gives
weighted absolute convergence of all their incidence entries at once. -/
theorem conductor_incidence_exhaustion {s : ℕ} {w u v : ℕ → ℝ} (hw : ∀ i, 0≤w i)
    (h : Summable (conductorIncidence s w u v)) (U V : ℕ → ℕ → ℝ)
    (hu : ∀ i, Tendsto (fun N => U N i) atTop (𝓝 (u i)))
    (hv : ∀ i, Tendsto (fun N => V N i) atTop (𝓝 (v i)))
    (hU : ∀ N i, |U N i| ≤ |u i|) (hV : ∀ N i, |V N i| ≤ |v i|) :
    Tendsto (fun N => ∑' p : ℕ × ℕ, w (p.2+1)*
      |U N (p.1+1)*V N ((p.2+1+s)*(p.1+1))-u (p.1+1)*v ((p.2+1+s)*(p.1+1))|) atTop (𝓝 0) := by
  refine pair_price_exhaustion (fun p : ℕ × ℕ => p.1+1) (fun p => (p.2+1+s)*(p.1+1))
    (fun p => w (p.2+1)) u v (fun p => hw _) (h.congr fun p => ?_) U V hu hv hU hV
  rw [abs_mul]
  unfold conductorIncidence
  ring

/-- Conductors through the cutoff, rounded toward zero and divided by
their common integer multiplicity. -/
def normalizedConductor (N : ℕ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i≤N then (roundedJump N (u i):ℝ)/((N:ℝ)+1) else 0

theorem normalizedConductor_abs (N : ℕ) (u : ℕ → ℝ) (i : ℕ) :
    |normalizedConductor N u i| ≤ |u i| := by
  by_cases h : i≤N
  · have hs : 0<(N:ℝ)+1 := by positivity
    have he : |(roundedJump N (u i):ℝ)| = (⌊((N:ℝ)+1)*|u i|⌋₊:ℝ) := by
      by_cases hx : u i<0 <;> simp [roundedJump,hx]
    rw [normalizedConductor,if_pos h,abs_div,he,abs_of_pos hs,div_le_iff₀ hs,mul_comm (|u i|)]
    exact Nat.floor_le (mul_nonneg hs.le (abs_nonneg _))
  · simpa only [normalizedConductor,if_neg h,abs_zero] using abs_nonneg (u i)

theorem normalizedConductor_tendsto (u : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun N => normalizedConductor N u i) atTop (𝓝 (u i)) := by
  have hs : Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have he := (tendsto_nat_floor_mul_div_atTop (abs_nonneg (u i))).comp hs
  simp only [Function.comp_def,Nat.cast_succ,mul_comm (|u i|)] at he
  have h : Tendsto (fun N : ℕ => (roundedJump N (u i):ℝ)/((N:ℝ)+1)) atTop (𝓝 (u i)) := by
    by_cases hx : u i<0
    · simpa only [roundedJump,if_pos hx,Int.cast_neg,Int.cast_natCast,neg_div,abs_of_neg hx,neg_neg] using he.neg
    · simpa only [roundedJump,if_neg hx,Int.cast_natCast,abs_of_nonneg (le_of_not_gt hx)] using he
  apply h.congr'
  filter_upwards [eventually_ge_atTop i] with N hN
  simp only [normalizedConductor,if_pos hN]

/-- Rounded conductors converge in each divisor's own weighted square
norm. The dominating square sequence is four times its original energy. -/
theorem normalizedConductor_energy_limit (r u : ℕ → ℝ)
    (hu : Summable (fun i => (r i*u i)^2)) :
    Tendsto (fun N => infiniteConductorNorm (fun i => r i*(normalizedConductor N u i-u i))) atTop (𝓝 0) := by
  let d := fun N i => r i*(normalizedConductor N u i-u i)
  have he (i : ℕ) : Tendsto (fun N => (d N i)^2) atTop (𝓝 0) := by
    simpa only [d,sub_self,mul_zero,zero_pow (by decide : 2≠0)] using
      ((((normalizedConductor_tendsto u i).sub_const (u i)).const_mul (r i)).pow 2)
  have hb (N i : ℕ) : ‖(d N i)^2‖≤4*(r i*u i)^2 := by
    have ha : |normalizedConductor N u i-u i|≤2*|u i| :=
      ((abs_sub _ _).trans (add_le_add (normalizedConductor_abs N u i) le_rfl)).trans_eq (two_mul _).symm
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ha 2) (sq_nonneg (r i))
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simp only [mul_pow,sq_abs] at h
    change (r i*(normalizedConductor N u i-u i))^2≤_
    rw [mul_pow]
    exact h.trans_eq (by ring)
  have hl := tendsto_tsum_of_dominated_convergence (hu.mul_left 4) he (Eventually.of_forall hb)
  simpa only [infiniteConductorNorm,d,tsum_zero,Real.sqrt_zero] using hl.sqrt

/-- The same array of actual integral endpoint jumps realizes every
positive normalized conductor in each cutoff. -/
theorem normalizedConductor_integral_endpoints (u : ℕ → ℝ) (N : ℕ) :
    ∃ a : ℕ → ℤ, ∀ i, 0 < i → (upperDivisor N a i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i := by
  obtain ⟨a,ha⟩ := exists_upper_endpoints N (fun i => roundedJump N (u i))
  refine ⟨a,fun i hi => ?_⟩
  rw [ha i hi,normalizedConductor]
  by_cases h : i≤N <;> simp [h]

/-- At any quotient shift the actual rounded integral conductors converge
in the absolute incidence sum. This controls the two consecutive tails
used to reconstruct a quotient cell. -/
theorem integral_incidence_exhaustion (s : ℕ) (r w u v : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (w k/r k)^2))
    (hu : Summable (fun i => (r i*u i)^2)) (hv : Summable (fun i => (r i*v i)^2)) :
    Tendsto (fun N => ∑' p : ℕ × ℕ, w (p.2+1)*
      |normalizedConductor N u (p.1+1)*normalizedConductor N v ((p.2+1+s)*(p.1+1))-
       u (p.1+1)*v ((p.2+1+s)*(p.1+1))|) atTop (𝓝 0) :=
  conductor_incidence_exhaustion hw (infinite_conductor_incidences s r w u v hr hm hw hA hB hu hv).1
    (fun N => normalizedConductor N u) (fun N => normalizedConductor N v)
    (normalizedConductor_tendsto u) (normalizedConductor_tendsto v)
    (fun N => normalizedConductor_abs N u) (fun N => normalizedConductor_abs N v)

/-- The two off-diagonal real monomials, with zero on the diagonal and at
the unused zero conductor. -/
def conductorJetEntry (i j : ℕ) (x : ℝ) : ℝ :=
  if 0 < i ∧ 0 < j ∧ i≠j then x^(max i j-min i j-1)+x^(i+j-1) else 0

/-- The pointwise jet of two infinite conductor sections. -/
def completedConductorJet (u v : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, u p.1*v p.2*conductorJetEntry p.1 p.2 x

/-- Each of the two real monomials has absolute value at most one. -/
theorem jet_entry_bound (i j : ℕ) {x : ℝ} (hx : x∈Set.Icc 0 1) :
    |conductorJetEntry i j x| ≤ 2 := by
  unfold conductorJetEntry
  split
  · rw [abs_of_nonneg (add_nonneg (pow_nonneg hx.1 _) (pow_nonneg hx.1 _))]
    linarith only [pow_le_one₀ (n := max i j-min i j-1) hx.1 hx.2,
      pow_le_one₀ (n := i+j-1) hx.1 hx.2]
  · norm_num

/-- Each normalized finite jet equals the real jet of its actual integral
endpoint presentation divided by the square of the rounding multiplicity. -/
theorem normalized_jet_eq_integral_section (N : ℕ) (u v : ℕ → ℝ) (a b : ℕ → ℤ)
    (ha : ∀ i, 0 < i → (upperDivisor N a i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i)
    (hb : ∀ i, 0 < i → (upperDivisor N b i:ℝ)/((N:ℝ)+1)=normalizedConductor N v i) (x : ℝ) :
    completedConductorJet (normalizedConductor N u) (normalizedConductor N v) x =
      mixedJetSection N a b x/((N:ℝ)+1)^2 := by
  let S := Icc 1 N
  unfold completedConductorJet
  rw [tsum_eq_sum (s := S×ˢS) (fun p hp => by
    by_cases hi : p.1∈S
    · have hj : p.2∉S := fun hj => hp (mem_product.mpr ⟨hi,hj⟩)
      by_cases hz : p.2=0
      · simp [conductorJetEntry,hz]
      · have hn : ¬p.2≤N := fun hle => hj (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hz,hle⟩)
        simp [normalizedConductor,hn]
    · by_cases hz : p.1=0
      · simp [conductorJetEntry,hz]
      · have hn : ¬p.1≤N := fun hle => hi (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hz,hle⟩)
        simp [normalizedConductor,hn]),sum_product,sum_comm]
  unfold mixedJetSection
  rw [sum_div]
  refine sum_congr rfl fun n hn => ?_
  have hdiag : normalizedConductor N u n*normalizedConductor N v n*conductorJetEntry n n x=0 := by
    simp [conductorJetEntry]
  rw [← sum_erase S (f := fun m => normalizedConductor N u m*normalizedConductor N v n*conductorJetEntry m n x) hdiag,sum_div]
  refine sum_congr rfl fun m hm => ?_
  have hmp := (mem_Icc.mp (mem_of_mem_erase hm)).1
  have hnp := (mem_Icc.mp hn).1
  rw [conductorJetEntry,if_pos ⟨hmp,hnp,(mem_erase.mp hm).1⟩,← ha _ hmp,← hb _ hnp]
  change _ = ((upperDivisor N a m:ℝ)*upperDivisor N b n*(x^(max m n-min m n-1)+x^(m+n-1)))/_
  simp only [div_eq_mul_inv,← inv_pow]
  ring

/-- Independent pointwise exhaustions bounded by the individual absolute
multiplicities converge uniformly in the real-place jet. -/
theorem dominated_jet_exhaustion (r u v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hA : Summable (fun k => (1/r k)^2))
    (hu : Summable (fun i => (r i*u i)^2)) (hv : Summable (fun i => (r i*v i)^2))
    (U V : ℕ → ℕ → ℝ) (hUt : ∀ i, Tendsto (fun N => U N i) atTop (𝓝 (u i)))
    (hVt : ∀ i, Tendsto (fun N => V N i) atTop (𝓝 (v i)))
    (hU : ∀ N i, |U N i| ≤ |u i|) (hV : ∀ N i, |V N i| ≤ |v i|) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ N x, x∈Set.Icc 0 1 →
      |completedConductorJet (U N) (V N) x-
        completedConductorJet u v x| ≤ e N := by
  have h₁ (f : ℕ → ℝ) (hf : Summable (fun k => (r k*f k)^2)) : Summable (fun i => |f i|) := by
    simpa only [one_mul,id_eq] using (infinite_weighted_row r (fun _ => 1) f hr hm
      (fun _ => zero_le_one) hA hf id Function.injective_id (fun _ => le_rfl)).1
  let P := fun p : ℕ × ℕ => u p.1*v p.2
  let Q := fun N (p : ℕ × ℕ) => U N p.1*V N p.2
  have hP : Summable (fun p => |P p|) := by
    have h := summable_mul_of_summable_norm (f := fun i => |u i|) (g := fun j => |v j|)
      (h₁ u hu).norm (h₁ v hv).norm
    simpa only [P,abs_mul] using h
  have hQ (N : ℕ) (p : ℕ × ℕ) : |Q N p| ≤ |P p| := by
    simp only [Q,P,abs_mul]
    exact mul_le_mul (hU N _) (hV N _) (abs_nonneg _) (abs_nonneg _)
  let D := fun N p => |Q N p-P p|
  have hdom (N : ℕ) (p : ℕ × ℕ) : D N p≤2* |P p| := by
    calc _ ≤ |Q N p|+|P p| := abs_sub _ _
         _ ≤ |P p|+|P p| := add_le_add (hQ N p) le_rfl
         _ = _ := (two_mul _).symm
  have hd (N : ℕ) : Summable (D N) := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hdom N) (hP.mul_left 2)
  have hlim : Tendsto (fun N => ∑' p, D N p) atTop (𝓝 0) := by
    simpa only [one_mul,D,Q,P] using pair_price_exhaustion Prod.fst Prod.snd (fun _ => 1) u v
      (fun _ => zero_le_one) (by simpa only [one_mul] using hP) U V hUt hVt hU hV
  refine ⟨fun N => (∑' p, D N p)*2,by simpa only [zero_mul] using hlim.mul_const 2,?_⟩
  intro N x hx
  let K := fun p : ℕ × ℕ => conductorJetEntry p.1 p.2 x
  have hk (p : ℕ × ℕ) : |K p|≤2 := jet_entry_bound _ _ hx
  have hPK (f : ℕ × ℕ → ℝ) (hf : ∀ p, |f p|≤|P p|) : Summable (fun p => f p*K p) := by
    apply (hP.mul_right 2).of_norm_bounded
    intro p
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hf p) (hk p) (abs_nonneg _) (abs_nonneg _)
  have hp := hPK P fun _ => le_rfl
  have hq := hPK (Q N) (hQ N)
  change |(∑' p, Q N p*K p)-(∑' p, P p*K p)| ≤ (∑' p, D N p)*2
  rw [← hq.tsum_sub hp,← tsum_mul_right]
  have he (p : ℕ × ℕ) : ‖Q N p*K p-P p*K p‖≤D N p*2 := by
    rw [← sub_mul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hk p) (abs_nonneg _)
  exact (norm_tsum_le_tsum_norm (hq.sub hp).norm).trans
    ((hq.sub hp).norm.tsum_le_tsum he ((hd N).mul_right 2))

/-- Both arbitrary supports exhaust in the uniform norm of the real jet.
The uniform majorant is twice the absolute mass of the coefficient
product error, which tends to zero on the same rounded conductors. -/
theorem uniform_jet_exhaustion (r u v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hA : Summable (fun k => (1/r k)^2))
    (hu : Summable (fun i => (r i*u i)^2)) (hv : Summable (fun i => (r i*v i)^2)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ N x, x∈Set.Icc 0 1 →
      |completedConductorJet (normalizedConductor N u) (normalizedConductor N v) x-
        completedConductorJet u v x| ≤ e N :=
  dominated_jet_exhaustion r u v hr hm hA hu hv (fun N => normalizedConductor N u) (fun N => normalizedConductor N v)
    (normalizedConductor_tendsto u) (normalizedConductor_tendsto v)
    (fun N => normalizedConductor_abs N u) (fun N => normalizedConductor_abs N v)

#print axioms dominated_jet_exhaustion
#print axioms normalizedConductor_energy_limit
#print axioms uniform_jet_exhaustion
#print axioms normalized_jet_eq_integral_section
#print axioms normalizedConductor_integral_endpoints
#print axioms integral_incidence_exhaustion
#print axioms infinite_conductor_incidences
#print axioms conductor_incidence_exhaustion
end GaloisForLFunctions.SignedArithmeticCorrespondences
