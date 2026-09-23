import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete

/-!
# Signed coefficient prefixes control complete physical energy

Finite Abel summation converts a bound on signed coefficient prefixes into a
bound for every cell of the original Báez-Duarte carrier. A separate coefficient
mass bound retains the whole infinite tail. The resulting energy estimate is
also stated using the actual finite maximum of normalized prefixes, with no
assumed cancellation estimate.

This is the transfer estimate needed to compare the prime-count endpoint
source with a summatory coefficient model. It does not estimate those
arithmetic prefixes or prove RH.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCoefficientTransfer

/-- Signed coefficient sum through the given cutoff. -/
def partialSum (a : ℕ → ℝ) (K : ℕ) : ℝ := ∑ i ∈ range K, a (i+1)
/-- Total coefficient mass through the cutoff. -/
def mass (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ range N, |a (i+1)|
/-- The finite harmonic weight entering the Abel estimate. -/
def harmonicMass (N : ℕ) : ℝ := ∑ i ∈ range N, 1/((i : ℝ)+1)
/-- The original physical source with arbitrary real coefficients. -/
def source (a : ℕ → ℝ) (N : ℕ) : BDCarrier :=
  ∑ i ∈ range N, (a (i+1) : ℂ) • bdGen (1/((i : ℝ)+1))
/-- Exact numerator on an integer physical cell. -/
def cell (a : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ i ∈ range N, a (i+1)*((k%(i+1) : ℕ) : ℝ)/((i : ℝ)+1)

private theorem abel_identity (a w : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, w i*a i) =
      w (N-1)*(∑ i ∈ range N,a i) +
        ∑ i ∈ range (N-1),(w i-w (i+1))*(∑ j ∈ range (i+1),a j) := by
  have h := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at h
  rw [h]
  simp only [sub_mul,Finset.sum_sub_distrib]
  ring

/-- Abel comparison retains the signed partialSum, before using positive decreasing weights. -/
theorem abs_weighted_sum_le (a w : ℕ → ℝ) (N : ℕ) {eps : ℝ}
    (hw : ∀ i, 0  ≤  w i) (hanti : Antitone w)
    (hp : ∀ K  ≤  N, |partialSum a K|  ≤  eps*(K : ℝ)) :
    |∑ i ∈ range N,w i*a (i+1)|  ≤  eps*∑ i ∈ range N,w i := by
  rw [abel_identity]
  calc
    _  ≤  |w (N-1)*partialSum a N| +
        ∑ i ∈ range (N-1),|(w i-w (i+1))*partialSum a (i+1)| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _  ≤  w (N-1)*(eps*(N : ℝ)) +
        ∑ i ∈ range (N-1),(w i-w (i+1))*(eps*((i+1 : ℕ) : ℝ)) := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg (hw _)]
        exact mul_le_mul_of_nonneg_left (hp N le_rfl) (hw _)
      · apply sum_le_sum
        intro i hi
        have hd : 0  ≤  w i-w (i+1) := sub_nonneg.mpr (hanti (by omega))
        rw [abs_mul,abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hp (i+1) (by have := mem_range.mp hi; omega)) hd
    _ = _ := by
      have h := abel_identity (fun _ => (1 : ℝ)) w N
      simp only [mul_one,sum_const,card_range,nsmul_eq_mul,mul_one] at h
      calc
        _ = eps*(w (N-1)*(N : ℝ)+
          ∑ i ∈ range (N-1),(w i-w (i+1))*((i+1 : ℕ) : ℝ)) := by
            rw [mul_add,mul_sum]
            congr 1
            · ring
            · apply sum_congr rfl
              intro i hi
              ring
        _ = _ := by rw [← h]

/-- Every cell is controlled using the harmonic and floor weights separately. -/
theorem abs_cell_le_prefix (a : ℕ → ℝ) (N k : ℕ) {eps : ℝ}
    (heps : 0  ≤  eps) (hp : ∀ K  ≤  N, |partialSum a K|  ≤  eps*(K : ℝ)) :
    |cell a N k|  ≤  2*eps*harmonicMass N*(k : ℝ) := by
  have hH := abs_weighted_sum_le a (fun i => 1/((i : ℝ)+1)) N
    (fun i => by positivity) (by
      intro i j hij
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)) hp
  have hF := abs_weighted_sum_le a (fun i => ((k/(i+1) : ℕ) : ℝ)) N
    (fun i => Nat.cast_nonneg _) (by
      intro i j hij
      have hdiv : k/(j+1) ≤ k/(i+1) :=
        Nat.div_le_div_left (Nat.add_le_add_right hij 1) (by omega : 0 < i+1)
      change ((k/(j+1) : ℕ) : ℝ) ≤ ((k/(i+1) : ℕ) : ℝ)
      exact Nat.cast_le.mpr hdiv) hp
  have hsumF : (∑ i ∈ range N,((k/(i+1) : ℕ) : ℝ))  ≤  (k : ℝ)*harmonicMass N := by
    rw [harmonicMass,mul_sum]
    apply sum_le_sum
    intro i hi
    have hle : ((k/(i+1) : ℕ) : ℝ)*((i : ℝ)+1)  ≤  k := by
      exact_mod_cast Nat.div_mul_le_self k (i+1)
    rw [mul_one_div,le_div_iff₀ (by positivity)]
    exact hle
  have he : cell a N k =
      (k : ℝ)*(∑ i ∈ range N,1/((i : ℝ)+1)*a (i+1)) -
        ∑ i ∈ range N,((k/(i+1) : ℕ) : ℝ)*a (i+1) := by
    rw [cell,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.div_add_mod k (i+1))
    push_cast at h
    have hn : (i : ℝ)+1  ≠  0 := by positivity
    rw [show ((k%(i+1) : ℕ) : ℝ)=(k : ℝ)-((i : ℝ)+1)*((k/(i+1) : ℕ) : ℝ) by linarith]
    field_simp
  rw [he]
  calc
    _  ≤  |(k : ℝ)*(∑ i ∈ range N,1/((i : ℝ)+1)*a (i+1))| +
        |∑ i ∈ range N,((k/(i+1) : ℕ) : ℝ)*a (i+1)| := abs_sub _ _
    _  ≤  (k : ℝ)*(eps*harmonicMass N)+eps*((k : ℝ)*harmonicMass N) := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg k)]
        exact mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg k)
      · exact hF.trans (mul_le_mul_of_nonneg_left hsumF heps)
    _ = _ := by ring

/-- The coefficient mass controls the complete tail of every cell series. -/
theorem abs_cell_le_mass (a : ℕ → ℝ) (N k : ℕ) : |cell a N k|  ≤  mass a N := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro i hi
  rw [abs_div,abs_mul,abs_of_nonneg (show 0 ≤ ((k%(i+1) : ℕ) : ℝ) from Nat.cast_nonneg _),abs_of_pos (by positivity : 0 < (i : ℝ)+1)]
  have hmod : ((k%(i+1) : ℕ) : ℝ)  ≤  (i : ℝ)+1 := by
    exact_mod_cast (Nat.mod_lt k (by omega : 0 < i+1)).le
  rw [div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left hmod (abs_nonneg _)

/-- The exact energy series includes all physical cells. -/
theorem hasSum_source_energy (a : ℕ → ℝ) (N : ℕ) :
    HasSum (fun j : ℕ => cell a N (j+1)^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2)))
      (‖source a N‖^(2 : ℕ)) := by
  have h := hasSum_sum (s := range N) (fun m hm =>
    hasSum_sum (s := range N) (fun n hn =>
      (hasSum_bdGram_discrete (by omega : 1 ≤ m+1) (by omega : 1 ≤ n+1)).mul_left
        (a (m+1)*a (n+1))))
  simp only [Nat.cast_add,Nat.cast_one] at h
  rw [bdGram_quadraticForm_eq_norm_sq] at h
  change HasSum _ (‖source a N‖^(2 : ℕ)) at h
  convert h using 1
  funext j
  simp only [cell,pow_two,sum_mul,mul_sum,sum_div]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring


private theorem tail_telescope (T L : ℕ) :
    (∑ i ∈ range L,1/((((i+T : ℕ) : ℝ)+1)*(((i+T : ℕ) : ℝ)+2))) =
      1/((T : ℝ)+1)-1/(((L+T : ℕ) : ℝ)+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    have hT : (T : ℝ)+1  ≠  0 := by positivity
    have hL : (L : ℝ)+(T : ℝ)+1  ≠  0 := by positivity
    have hL2 : (L : ℝ)+(T : ℝ)+2  ≠  0 := by positivity
    field_simp
    ring

/-- An explicit complete-energy bound; the complementary tail is not dropped. -/
theorem source_energy_le (a : ℕ → ℝ) (N T : ℕ) {eps : ℝ}
    (heps : 0  ≤  eps) (hp : ∀ K  ≤  N, |partialSum a K|  ≤  eps*(K : ℝ)) :
    ‖source a N‖^(2 : ℕ)  ≤  4*(T : ℝ)*(eps*harmonicMass N)^(2 : ℕ)+
      mass a N^(2 : ℕ)/((T : ℝ)+1) := by
  let A : ℝ := 2*eps*harmonicMass N
  let W : ℝ := mass a N
  let f (j : ℕ) : ℝ := cell a N (j+1)^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2))
  have hhead (j : ℕ) : f j  ≤  A^(2 : ℕ) := by
    have h := abs_cell_le_prefix a N (j+1) heps hp
    change |cell a N (j+1)|  ≤  A*((j+1 : ℕ) : ℝ) at h
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hs
    dsimp [f]
    rw [div_le_iff₀ (by positivity)]
    push_cast at hs
    nlinarith [sq_nonneg A,mul_nonneg (sq_nonneg A) (show 0 ≤ (j : ℝ)+1 by positivity)]
  have htail (j : ℕ) : f j  ≤  W^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2)) := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (abs_cell_le_mass a N (j+1)) 2
    rw [sq_abs] at hs
    exact div_le_div_of_nonneg_right hs (by positivity)
  have hbound (K : ℕ) : (∑ j ∈ range K,f j)  ≤  (T : ℝ)*A^(2 : ℕ)+W^(2 : ℕ)/((T : ℝ)+1) := by
    by_cases hKT : K ≤ T
    · calc
        _  ≤  ∑ j ∈ range K,A^(2 : ℕ) := sum_le_sum (fun j _ => hhead j)
        _ = (K : ℝ)*A^(2 : ℕ) := by simp
        _  ≤  (T : ℝ)*A^(2 : ℕ) := mul_le_mul_of_nonneg_right (by exact_mod_cast hKT) (sq_nonneg _)
        _  ≤  _ := le_add_of_nonneg_right (by positivity)
    · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le (by omega : T ≤ K)
      subst K
      rw [sum_range_add]
      have hfirst : (∑ j ∈ range T,f j)  ≤  (T : ℝ)*A^(2 : ℕ) := by
        calc
          _  ≤  ∑ _j ∈ range T,A^(2 : ℕ) := sum_le_sum (fun j _ => hhead j)
          _ = _ := by simp
      have hlast : (∑ i ∈ range L,f (T+i))  ≤  W^(2 : ℕ)/((T : ℝ)+1) := by
        calc
          _  ≤  ∑ i ∈ range L,W^(2 : ℕ)/((((i+T : ℕ) : ℝ)+1)*(((i+T : ℕ) : ℝ)+2)) := by
            apply sum_le_sum
            intro i hi
            simpa only [Nat.add_comm T i] using htail (T+i)
          _ = W^(2 : ℕ)*(1/((T : ℝ)+1)-1/(((L+T : ℕ) : ℝ)+1)) := by
            calc
              _ = W^(2 : ℕ)*∑ i ∈ range L,1/((((i+T : ℕ) : ℝ)+1)*(((i+T : ℕ) : ℝ)+2)) := by
                rw [mul_sum]
                apply sum_congr rfl
                intro i hi
                ring
              _ = _ := by rw [tail_telescope]
          _  ≤  _ := by
            simp only [div_eq_mul_inv,one_mul]
            exact mul_le_mul_of_nonneg_left
              (sub_le_self (((T : ℝ)+1)⁻¹) (by positivity : 0 ≤ (((L+T : ℕ) : ℝ)+1)⁻¹))
              (sq_nonneg W)
      exact add_le_add hfirst hlast
  have h := le_of_tendsto (hasSum_source_energy a N).tendsto_sum_nat
    (Eventually.of_forall hbound)
  calc
    _ ≤ (T : ℝ)*A^(2 : ℕ)+W^(2 : ℕ)/((T : ℝ)+1) := h
    _ = _ := by dsimp [A,W]; ring


/-- The actual finite maximum of normalized signed prefixes, including the zero prefix. -/
def prefixEnvelope (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (range (N+1)).sup' (by simp) (fun k => |partialSum a k|/(k : ℝ))

theorem prefixEnvelope_nonneg (a : ℕ → ℝ) (N : ℕ) : 0 ≤ prefixEnvelope a N := by
  have h := Finset.le_sup' (f := fun k => |partialSum a k|/(k : ℝ))
    (mem_range.mpr (show 0<N+1 by omega))
  simpa only [Nat.cast_zero,div_zero] using! h

theorem abs_partialSum_le_envelope (a : ℕ → ℝ) {N K : ℕ} (hK : K ≤ N) :
    |partialSum a K| ≤ prefixEnvelope a N*(K : ℝ) := by
  by_cases h0 : K=0
  · subst K
    simp [partialSum]
  have h := Finset.le_sup' (f := fun k => |partialSum a k|/(k : ℝ))
    (mem_range.mpr (show K<N+1 by omega))
  exact (div_le_iff₀ (by exact_mod_cast (show 0<K by omega))).mp h

/-- Closed finite bound in terms of measured coefficient data; there is no assumed estimate. -/
theorem source_energy_le_envelope (a : ℕ → ℝ) (N T : ℕ) :
    ‖source a N‖^(2 : ℕ) ≤ 4*(T : ℝ)*(prefixEnvelope a N*harmonicMass N)^(2 : ℕ)+
      mass a N^(2 : ℕ)/((T : ℝ)+1) :=
  source_energy_le a N T (prefixEnvelope_nonneg a N)
    (fun _K hK => abs_partialSum_le_envelope a hK)


end RHTower.DeletionCoefficientTransfer
