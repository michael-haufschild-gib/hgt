import GaloisForLFunctions.SignedArithmeticCorrespondences.AbsoluteConductorIncidencesInTheCompletion
import GaloisForLFunctions.SignedArithmeticCorrespondences.TheSignedPrimeSumOfTheConductorTails

/-!
# The completed Weil intersection of two independently priced sections

Rounding the actual conductors and then taking endpoint jumps realizes
the signed prime and real terms at every cutoff. Absolute convergence
allows independent exhaustion of the two divisors. No condition is
placed on the ordering of their supports.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

private theorem positive_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range N, f (k+1))=∑ k ∈ Icc 1 N, f k := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih,sum_Icc_succ_top (by omega)]

/-- Directed local price on the actual multiplicity at every multiple. -/
def completedMultiplePrice (p u v : ℕ → ℝ) : ℝ :=
  ∑' t : ℕ × ℕ, u (t.1+1)*v ((t.2+1)*(t.1+1))*p (t.2+1)

private theorem normalized_multiple_price (N : ℕ) (p u v : ℕ → ℝ) (a b : ℕ → ℤ)
    (ha : ∀ i, 0 < i → (upperDivisor N a i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i)
    (hb : ∀ i, 0 < i → (upperDivisor N b i:ℝ)/((N:ℝ)+1)=normalizedConductor N v i) :
    completedMultiplePrice p (normalizedConductor N u) (normalizedConductor N v) =
      (∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 N, (upperDivisor N a i:ℝ)*upperDivisor N b (k*i)*p k)/
        ((N:ℝ)+1)^2 := by
  unfold completedMultiplePrice
  rw [tsum_eq_sum (s := (range N)×ˢ(range N)) (fun t ht => by
    by_cases hi : t.1<N
    · have hk : ¬t.2<N := fun hk => ht (mem_product.mpr ⟨mem_range.mpr hi,mem_range.mpr hk⟩)
      have hg := Nat.le_mul_of_pos_right (t.2+1) (Nat.succ_pos t.1)
      simp [normalizedConductor,show ¬(t.2+1)*(t.1+1)≤N by omega]
    · simp [normalizedConductor,show ¬t.1+1≤N by omega]),sum_product,sum_comm]
  rw [positive_sum (fun k => ∑ i ∈ range N,
    normalizedConductor N u (i+1)*normalizedConductor N v (k*(i+1))*p k),sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [positive_sum (fun i => normalizedConductor N u i*normalizedConductor N v (k*i)*p k),sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [← ha i (mem_Icc.mp hi).1,← hb (k*i) (Nat.mul_pos (mem_Icc.mp hk).1 (mem_Icc.mp hi).1)]
  simp only [div_eq_mul_inv,← inv_pow]
  ring

private theorem rounded_multiple_price_limit (r p u v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (|p k| / r k)^2))
    (hu : Summable (fun k => (r k*u k)^2)) (hv : Summable (fun k => (r k*v k)^2)) :
    Tendsto (fun N => completedMultiplePrice p (normalizedConductor N u) (normalizedConductor N v))
      atTop (𝓝 (completedMultiplePrice p u v)) := by
  have hs := (infinite_conductor_incidences 0 r (fun k => |p k|) u v hr hm (fun k => abs_nonneg _) hA hB hu hv).1
  let H (N : ℕ) (t : ℕ × ℕ) := normalizedConductor N u (t.1+1)*
    normalizedConductor N v ((t.2+1)*(t.1+1))*p (t.2+1)
  have he (t : ℕ × ℕ) : Tendsto (fun N => H N t) atTop
      (𝓝 (u (t.1+1)*v ((t.2+1)*(t.1+1))*p (t.2+1))) :=
    ((normalizedConductor_tendsto u _).mul (normalizedConductor_tendsto v _)).mul_const _
  apply tendsto_tsum_of_dominated_convergence hs he (Eventually.of_forall ?_)
  intro N t
  rw [Real.norm_eq_abs]
  simp only [H,abs_mul,conductorIncidence,Nat.add_zero]
  calc _ ≤ (|u (t.1+1)| * |v ((t.2+1)*(t.1+1))|)* |p (t.2+1)| :=
          mul_le_mul_of_nonneg_right (mul_le_mul (normalizedConductor_abs N u _) (normalizedConductor_abs N v _)
            (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
       _ = _ := by ring

/-- The limiting jet is continuous on the integration interval. Its
integral is the limit of the finite real-place integrals. -/
theorem completed_jet_integral_limit (r u v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hA : Summable (fun k => (1/r k)^2))
    (hu : Summable (fun k => (r k*u k)^2)) (hv : Summable (fun k => (r k*v k)^2)) :
    ContinuousOn (completedConductorJet u v) (Set.Icc 0 1) ∧
    Tendsto (fun N => ∫ x in (0:ℝ)..1, completedConductorJet (normalizedConductor N u) (normalizedConductor N v) x)
      atTop (𝓝 (∫ x in (0:ℝ)..1, completedConductorJet u v x)) := by
  let F := fun N => completedConductorJet (normalizedConductor N u) (normalizedConductor N v)
  let G := completedConductorJet u v
  obtain ⟨e,he,herr⟩ := uniform_jet_exhaustion r u v hr hm hA hu hv
  have hF (N : ℕ) : Continuous (F N) := by
    obtain ⟨a,ha⟩ := normalizedConductor_integral_endpoints u N
    obtain ⟨b,hb⟩ := normalizedConductor_integral_endpoints v N
    have hf : F N=fun x => mixedJetSection N a b x/((N:ℝ)+1)^2 :=
      funext (normalized_jet_eq_integral_section N u v a b ha hb)
    rw [hf]
    apply Continuous.div_const
    change Continuous (fun x : ℝ => ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (upperDivisor N a m:ℝ)*upperDivisor N b n*(x^(max m n-min m n-1)+x^(m+n-1)))
    fun_prop
  have hU : TendstoUniformlyOn F G atTop (Set.Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [he.eventually (Iio_mem_nhds hε)] with N hN
    intro x hx
    rw [dist_comm,Real.dist_eq]
    exact (herr N x hx).trans_lt hN
  have hG := hU.continuousOn (Eventually.of_forall fun N => (hF N).continuousOn).frequently
  refine ⟨hG,tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  apply squeeze_zero (fun _ => dist_nonneg _ _) _ he
  intro N
  change dist (∫ x in (0:ℝ)..1, F N x) (∫ x in (0:ℝ)..1, G x) ≤ e N
  rw [Real.dist_eq,← intervalIntegral.integral_sub ((hF N).intervalIntegrable 0 1)
    (hG.intervalIntegrable_of_Icc zero_le_one)]
  calc _ ≤ ∫ x in (0:ℝ)..1, |F N x-G x| := intervalIntegral.abs_integral_le_integral_abs zero_le_one
       _ ≤ ∫ _ in (0:ℝ)..1, e N := intervalIntegral.integral_mono_on zero_le_one
         (((hF N).continuousOn.sub hG).abs.intervalIntegrable_of_Icc zero_le_one)
         (continuous_const.intervalIntegrable 0 1) (herr N)
       _ = _ := by simp

/-- The same two integral divisor families recover the full signed
intersection for every pair of independently square-integrable conductor
sections with square-summable reciprocal and centered prime prices. -/
theorem completed_interleaved_integral_realization (r u v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (|Λ k-1| / r k)^2))
    (hu : Summable (fun k => (r k*u k)^2)) (hv : Summable (fun k => (r k*v k)^2)) :
    ∃ A B : ℕ → ℕ → ℤ,
      (∀ N i, 0 < i → (upperDivisor N (A N) i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i) ∧
      (∀ N i, 0 < i → (upperDivisor N (B N) i:ℝ)/((N:ℝ)+1)=normalizedConductor N v i) ∧
      Tendsto (fun N => interleavedFinitePart N (A N) (B N)/((N:ℝ)+1)^2) atTop
        (𝓝 (-(completedMultiplePrice (fun k => Λ k-1) u v+completedMultiplePrice (fun k => Λ k-1) v u)-
          (∫ x in (0:ℝ)..1, completedConductorJet u v x)/2)) := by
  choose A hA' using normalizedConductor_integral_endpoints u
  choose B hB' using normalizedConductor_integral_endpoints v
  let p := fun k => Λ k-1
  have hp := rounded_multiple_price_limit r p u v hr hm hA hB hu hv
  have hq := rounded_multiple_price_limit r p v u hr hm hA hB hv hu
  have hJ := (completed_jet_integral_limit r u v hr hm hA hu hv).2
  refine ⟨A,B,hA',hB',((hp.add hq).neg.sub (hJ.div_const 2)).congr fun N => ?_⟩
  have hjet : (fun x => completedConductorJet (normalizedConductor N u) (normalizedConductor N v) x)=
      (fun x => mixedJetSection N (A N) (B N) x/((N:ℝ)+1)^2) :=
    funext (normalized_jet_eq_integral_section N u v (A N) (B N) (hA' N) (hB' N))
  change -(completedMultiplePrice p (normalizedConductor N u) (normalizedConductor N v)+
    completedMultiplePrice p (normalizedConductor N v) (normalizedConductor N u))-
    (∫ x in (0:ℝ)..1, completedConductorJet (normalizedConductor N u) (normalizedConductor N v) x)/2=
      interleavedFinitePart N (A N) (B N)/((N:ℝ)+1)^2
  rw [normalized_multiple_price N p u v _ _ (hA' N) (hB' N),
    normalized_multiple_price N p v u _ _ (hB' N) (hA' N),hjet,intervalIntegral.integral_div,
    interleaved_centered_prime_sum]
  simp only [twoSidedMultiple,sum_add_distrib,sum_mul,add_mul,p]
  ring

/-- On the open half-power range every pair of infinite power-energy
sections is realized by integral Weil divisors at the two places. -/
theorem completed_power_integral_realization {s : ℝ} (hs : 1/2 < s) (u v : ℕ → ℝ)
    (hu : Summable (fun k => (powerConductorWeight s k*u k)^2))
    (hv : Summable (fun k => (powerConductorWeight s k*v k)^2)) :
    ∃ A B : ℕ → ℕ → ℤ,
      (∀ N i, 0 < i → (upperDivisor N (A N) i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i) ∧
      (∀ N i, 0 < i → (upperDivisor N (B N) i:ℝ)/((N:ℝ)+1)=normalizedConductor N v i) ∧
      Tendsto (fun N => interleavedFinitePart N (A N) (B N)/((N:ℝ)+1)^2) atTop
        (𝓝 (-(completedMultiplePrice (fun k => Λ k-1) u v+completedMultiplePrice (fun k => Λ k-1) v u)-
          (∫ x in (0:ℝ)..1, completedConductorJet u v x)/2)) := by
  obtain ⟨hr,hm,hA,hB⟩ := centered_prime_power_prices hs
  exact completed_interleaved_integral_realization _ u v hr hm hA hB hu hv

/-- A single actual conductor with multiplicity one. -/
def conductorAtom (i n : ℕ) : ℝ := if n=i then 1 else 0

private theorem directed_atom_price (p : ℕ → ℝ) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    completedMultiplePrice p (conductorAtom i) (conductorAtom j)=if i∣j then p (j/i) else 0 := by
  unfold completedMultiplePrice
  have hit (t : ℕ × ℕ) (h₁ : t.1+1=i) (h₂ : (t.2+1)*(t.1+1)=j) :
      i∣j ∧ t=(i-1,j/i-1) := by
    rw [h₁] at h₂
    have hq : t.2+1=j/i := by rw [← h₂,Nat.mul_div_cancel _ hi]
    exact ⟨⟨t.2+1,by rw [← h₂,Nat.mul_comm]⟩,Prod.ext (by omega) (by omega)⟩
  by_cases hd : i∣j
  · rw [if_pos hd,tsum_eq_single (i-1,j/i-1)]
    · have hq : 0 < j/i := Nat.div_pos (Nat.le_of_dvd hj hd) hi
      simp [conductorAtom,show i-1+1=i by omega,show j/i-1+1=j/i by omega,Nat.div_mul_cancel hd]
    · intro t hne
      by_cases h₁ : t.1+1=i
      · have h₂ : (t.2+1)*(t.1+1)≠j := fun h => hne (hit t h₁ h).2
        simp [conductorAtom,h₂]
      · simp [conductorAtom,h₁]
  · rw [if_neg hd]
    trans ∑' _ : ℕ × ℕ, (0:ℝ)
    · apply tsum_congr
      intro t
      by_cases h₁ : t.1+1=i
      · have h₂ : (t.2+1)*(t.1+1)≠j := fun h => hd (hit t h₁ h).1
        simp [conductorAtom,h₂]
      · simp [conductorAtom,h₁]
    · exact tsum_zero

private theorem atom_jet (i j : ℕ) (x : ℝ) :
    completedConductorJet (conductorAtom i) (conductorAtom j) x=conductorJetEntry i j x := by
  unfold completedConductorJet
  rw [tsum_eq_single (i,j)]
  · simp [conductorAtom]
  · intro t ht
    by_cases h : t.1=i
    · have hn : t.2≠j := fun hj => ht (Prod.ext h hj)
      simp [conductorAtom,hn]
    · simp [conductorAtom,h]

/-- Entries of the completed signed matrix on positive conductors. -/
def signedConductorEntry (i j : ℕ) : ℝ :=
  (if i∣j then 1-Λ (j/i) else 0)+(if j∣i then 1-Λ (i/j) else 0)-
    (∫ x in (0:ℝ)..1, conductorJetEntry i j x)/2

/-- The two divisibility orientations and the integrated off-diagonal
jet are the exact entries of the signed completed form. -/
theorem completed_signed_atom_entry {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    -(completedMultiplePrice (fun k => Λ k-1) (conductorAtom i) (conductorAtom j)+
      completedMultiplePrice (fun k => Λ k-1) (conductorAtom j) (conductorAtom i))-
      (∫ x in (0:ℝ)..1, completedConductorJet (conductorAtom i) (conductorAtom j) x)/2 = signedConductorEntry i j := by
  rw [directed_atom_price _ hi hj,directed_atom_price _ hj hi,signedConductorEntry]
  simp only [atom_jet]
  by_cases h : i∣j <;> by_cases h' : j∣i <;> simp [h,h'] <;> ring

/-- Each positive diagonal entry equals two. -/
theorem signedConductorEntry_diagonal {i : ℕ} (hi : 0 < i) : signedConductorEntry i i=2 := by
  simp [signedConductorEntry,Nat.div_self hi,conductorJetEntry]
  <;> norm_num

/-- Absolute column entries grow at most logarithmically in the two
conductors, including their common diagonal. -/
theorem signedConductorEntry_bound {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    |signedConductorEntry i j| ≤ 3+Real.log i+Real.log j := by
  have price {a b : ℕ} (hb : 0 < b) :
      |if a∣b then 1-Λ (b/a) else 0|≤1+Real.log b := by
    by_cases h : a∣b
    · have ha : 0 < a := Nat.pos_of_dvd_of_pos h hb
      have hq : 0 < b/a := Nat.div_pos (Nat.le_of_dvd hb h) ha
      have hl := Real.log_le_log (Nat.cast_pos.mpr hq : (0:ℝ) < ((b/a:ℕ):ℝ)) (Nat.cast_le.mpr (Nat.div_le_self b a))
      rw [if_pos h]
      apply (abs_sub _ _).trans
      rw [abs_one,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact add_le_add_left (ArithmeticFunction.vonMangoldt_le_log.trans hl) 1
    · rw [if_neg h,abs_zero]
      exact add_nonneg zero_le_one (Real.log_natCast_nonneg _)
  have hJ : Continuous (conductorJetEntry i j) := by
    by_cases he : i=j <;> simp [conductorJetEntry,hi,hj,he] <;> fun_prop
  have hInt : |∫ x in (0:ℝ)..1, conductorJetEntry i j x|≤2 := by
    apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun x => |conductorJetEntry i j x|)
      (g := fun _ => (2:ℝ)) zero_le_one (hJ.abs.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) (fun _ hx => jet_entry_bound i j hx)
    simpa using h
  unfold signedConductorEntry
  apply (abs_sub _ _).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hp := (abs_add_le _ _).trans (add_le_add (price (a := i) hj) (price (a := j) hi))
  linarith only [hp,hInt]

#print axioms signedConductorEntry_diagonal
#print axioms signedConductorEntry_bound
#print axioms completed_signed_atom_entry

private def cellEntry (w u v : ℕ → ℝ) (t : ℕ × ℕ) : ℝ :=
  let i := t.1+1
  let k := t.2+1
  w k*((u i*v (k*i)+v i*u (k*i))-(u i*v ((k+1)*i)+v i*u ((k+1)*i)))

/-- Completed weighted quotient cell indexed by k+1. Grouping is performed
after multiplying by its price, so zero prices are allowed. -/
def completedWeightedCell (w u v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' i, cellEntry w u v (i,k)

private def cellMajorant (w u v : ℕ → ℝ) (t : ℕ × ℕ) : ℝ :=
  (conductorIncidence 0 w u v t+conductorIncidence 0 w v u t)+
  (conductorIncidence 1 w u v t+conductorIncidence 1 w v u t)

private theorem cellEntry_le {w u v U V : ℕ → ℝ} (hw : ∀ k, 0≤w k)
    (hU : ∀ i, |U i|≤|u i|) (hV : ∀ i, |V i|≤|v i|) (t : ℕ × ℕ) :
    |cellEntry w U V t| ≤ cellMajorant w u v t := by
  let i := t.1+1
  let k := t.2+1
  have term {f g f' g' : ℕ → ℝ} (hf : ∀ j, |f j| ≤ |f' j|) (hg : ∀ j, |g j| ≤ |g' j|) (s : ℕ) :
      w k* |f i*g ((k+s)*i)| ≤ conductorIncidence s w f' g' t := by
    rw [abs_mul]
    calc _ ≤ w k*(|f' i| * |g' ((k+s)*i)|) := mul_le_mul_of_nonneg_left
           (mul_le_mul (hf _) (hg _) (abs_nonneg _) (abs_nonneg _)) (hw k)
         _ = _ := by dsimp [conductorIncidence,i,k]; ring
  have hp (j : ℕ) : |U i*V (j*i)+V i*U (j*i)| ≤ |U i*V (j*i)|+|V i*U (j*i)| := abs_add_le _ _
  rw [cellEntry,abs_mul,abs_of_nonneg (hw _)]
  calc _ ≤ w k*((|U i*V (k*i)|+|V i*U (k*i)|)+(|U i*V ((k+1)*i)|+|V i*U ((k+1)*i)|)) :=
         mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hp k) (hp (k+1)))) (hw k)
       _ ≤ _ := by
         simp only [mul_add]
         exact add_le_add (add_le_add (term hU hV 0) (term hV hU 0))
           (add_le_add (term hU hV 1) (term hV hU 1))

/-- A signed absolutely summable matrix can be grouped by its columns
without increasing total absolute variation. -/
private theorem column_variation (z : ℕ × ℕ → ℝ) (hz : Summable (fun t => |z t|)) :
    Summable (fun k => |∑' i, z (i,k)|) ∧ (∑' k, |∑' i, z (i,k)|) ≤ ∑' t, |z t| := by
  have h := (summable_prod_of_nonneg (f := fun t : ℕ × ℕ => |z (t.2,t.1)|) (fun _ => abs_nonneg _)).mp hz.prod_symm
  have hb (k : ℕ) : |∑' i, z (i,k)| ≤ ∑' i, |z (i,k)| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun i => z (i,k)) (by simpa only [Real.norm_eq_abs] using h.1 k)
  have hs := Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb h.2
  refine ⟨hs,(hs.tsum_le_tsum hb h.2).trans_eq ?_⟩
  rw [hz.tsum_prod]
  exact Summable.tsum_comm (f := fun i k => |z (i,k)|) hz

/-- Independent dominated exhaustions converge in weighted absolute
variation after taking the difference of the two multiplicative tails. -/
theorem dominated_weighted_cell_exhaustion (r w u v : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (w k/r k)^2))
    (hu : Summable (fun k => (r k*u k)^2)) (hv : Summable (fun k => (r k*v k)^2))
    (U V : ℕ → ℕ → ℝ) (hUt : ∀ i, Tendsto (fun N => U N i) atTop (𝓝 (u i)))
    (hVt : ∀ i, Tendsto (fun N => V N i) atTop (𝓝 (v i)))
    (hU : ∀ N i, |U N i| ≤ |u i|) (hV : ∀ N i, |V N i| ≤ |v i|) :
    Summable (fun k => |completedWeightedCell w u v k|) ∧
      Tendsto (fun N => ∑' k, |completedWeightedCell w (U N) (V N) k-
        completedWeightedCell w u v k|) atTop (𝓝 0) := by
  let P := cellEntry w u v
  let Q := fun N => cellEntry w (U N) (V N)
  let M := cellMajorant w u v
  have hs (s : ℕ) := (infinite_conductor_incidences s r w u v hr hm hw hA hB hu hv).1
  have ht (s : ℕ) := (infinite_conductor_incidences s r w v u hr hm hw hA hB hv hu).1
  have hM : Summable M := ((hs 0).add (ht 0)).add ((hs 1).add (ht 1))
  have hp (t : ℕ × ℕ) : |P t|≤M t := cellEntry_le hw (fun _ => le_rfl) (fun _ => le_rfl) t
  have hq (N : ℕ) (t : ℕ × ℕ) : |Q N t|≤M t :=
    cellEntry_le hw (hU N) (hV N) t
  have hP := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hp hM
  have hQ (N : ℕ) := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hq N) hM
  have hD (N : ℕ) (t : ℕ × ℕ) : |Q N t-P t|≤2*M t := by
    rw [two_mul]
    exact (abs_sub _ _).trans (add_le_add (hq N t) (hp t))
  have hlim (t : ℕ × ℕ) : Tendsto (fun N => |Q N t-P t|) atTop (𝓝 0) := by
    let i := t.1+1
    let k := t.2+1
    have ht (j : ℕ) := ((hUt i).mul (hVt (j*i))).add
      ((hVt i).mul (hUt (j*i)))
    have he : Tendsto (fun N => Q N t) atTop (𝓝 (P t)) := ((ht k).sub (ht (k+1))).const_mul (w k)
    simpa only [sub_self,abs_zero] using (he.sub_const (P t)).abs
  have htot := tendsto_tsum_of_dominated_convergence (hM.mul_left 2) hlim
    (Eventually.of_forall (fun N t => by simpa only [Real.norm_eq_abs,abs_abs] using hD N t))
  simp only [tsum_zero] at htot
  refine ⟨(column_variation P hP).1,squeeze_zero (fun _ => tsum_nonneg fun _ => abs_nonneg _) ?_ htot⟩
  intro N
  have hd := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hD N) (hM.mul_left 2)
  apply le_trans (le_of_eq ?_) (column_variation (fun t => Q N t-P t) hd).2
  apply tsum_congr
  intro k
  have hsP : Summable (fun i => P (i,k)) := ((hP.prod_symm.prod_factor k).of_abs)
  have hsQ : Summable (fun i => Q N (i,k)) := (((hQ N).prod_symm.prod_factor k).of_abs)
  change |(∑' i, Q N (i,k))-(∑' i, P (i,k))| = |∑' i, Q N (i,k)-P (i,k)|
  exact congrArg abs (hsQ.tsum_sub hsP).symm

/-- The full sequence of weighted quotient cells of normalized conductors
converges in absolute variation, with both supports growing together. -/
theorem completed_weighted_cell_exhaustion (r w u v : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hA : Summable (fun k => (1/r k)^2)) (hB : Summable (fun k => (w k/r k)^2))
    (hu : Summable (fun k => (r k*u k)^2)) (hv : Summable (fun k => (r k*v k)^2)) :
    Summable (fun k => |completedWeightedCell w u v k|) ∧
      Tendsto (fun N => ∑' k, |completedWeightedCell w (normalizedConductor N u) (normalizedConductor N v) k-
        completedWeightedCell w u v k|) atTop (𝓝 0) :=
  dominated_weighted_cell_exhaustion r w u v hr hm hw hA hB hu hv
    (fun N => normalizedConductor N u) (fun N => normalizedConductor N v)
    (normalizedConductor_tendsto u) (normalizedConductor_tendsto v)
    (fun N => normalizedConductor_abs N u) (fun N => normalizedConductor_abs N v)

#print axioms dominated_weighted_cell_exhaustion

/-- At every cutoff the weighted completed cells of the rounded sections
are exactly the positive quotient cells of the two scaled integral
endpoint divisors, extended by zero past the cutoff. -/
theorem normalized_weighted_cell_eq (N k : ℕ) (w u v : ℕ → ℝ) (a b : ℕ → ℤ)
    (ha : ∀ i, 0 < i → (upperDivisor N a i:ℝ)/((N:ℝ)+1)=normalizedConductor N u i)
    (hb : ∀ i, 0 < i → (upperDivisor N b i:ℝ)/((N:ℝ)+1)=normalizedConductor N v i) :
    completedWeightedCell w (normalizedConductor N u) (normalizedConductor N v) k =
      if k<N then w (k+1)*twoSidedCoefficient N a b (k+1)/((N:ℝ)+1)^2 else 0 := by
  let q := k+1
  let U := normalizedConductor N u
  let V := normalizedConductor N v
  let t := fun j i => (upperDivisor N a i:ℝ)*upperDivisor N b (j*i)+(upperDivisor N b i:ℝ)*upperDivisor N a (j*i)
  let f (i : ℕ) := w q*((U i*V (q*i)+V i*U (q*i))-(U i*V ((q+1)*i)+V i*U ((q+1)*i)))
  change (∑' i : ℕ, f (i+1))=_
  rw [tsum_eq_sum (s := range N) (fun i hi => by
    have h := mem_range.not.mp hi
    simp [f,U,V,normalizedConductor,show ¬i+1≤N by omega]),positive_sum]
  by_cases hk : k<N
  · rw [if_pos hk]
    have he (i : ℕ) (hi : i∈Icc 1 N) :
        f i=(w q/((N:ℝ)+1)^2)*(t q i-t (q+1) i) := by
      have hi₀ := (mem_Icc.mp hi).1
      have hq := Nat.mul_pos (Nat.succ_pos k) hi₀
      have hq' := Nat.mul_pos (Nat.succ_pos q) hi₀
      dsimp only [f,U,V,t]
      rw [← ha _ hi₀,← hb _ hi₀,← ha _ hq,← hb _ hq,← ha _ hq',← hb _ hq']
      simp only [div_eq_mul_inv,← inv_pow]
      ring
    rw [sum_congr rfl he,← mul_sum,sum_sub_distrib]
    have hc : twoSidedCoefficient N a b q=(∑ i ∈ Icc 1 N, t q i)-∑ i ∈ Icc 1 N, t (q+1) i :=
      twoSidedCoefficient_difference hk a b
    rw [← hc]
    ring
  · rw [if_neg hk]
    apply sum_eq_zero
    intro i hi
    have h₁ := Nat.le_mul_of_pos_right q (mem_Icc.mp hi).1
    have h₂ := Nat.le_mul_of_pos_right (q+1) (mem_Icc.mp hi).1
    have hq : N<q := by dsimp [q]; omega
    simp [f,U,V,normalizedConductor,show ¬q*i≤N by omega,show ¬(q+1)*i≤N by omega]

#print axioms normalized_weighted_cell_eq
#print axioms completed_weighted_cell_exhaustion
#print axioms completed_power_integral_realization
#print axioms completed_jet_integral_limit
#print axioms completed_interleaved_integral_realization
end GaloisForLFunctions.SignedArithmeticCorrespondences
