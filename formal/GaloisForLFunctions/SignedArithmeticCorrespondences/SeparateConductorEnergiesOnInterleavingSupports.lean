import GaloisForLFunctions.SignedArithmeticCorrespondences.TheIntegralRangeOfTheMixedQuotientCells

/-!
# Separate conductor energies for interleaving integral divisors

The first differences of the multiplicative correlations charge each
directed contact to two independently weighted conductor norms. The
off-diagonal real section is bounded in the same norms on the whole
unit interval.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory

/-- Euclidean mass on the actual positive conductors through the cutoff. -/
def conductorNorm (N : ℕ) (v : ℕ → ℝ) : ℝ :=
  Real.sqrt (∑ n ∈ Icc 1 N, v n ^ 2)

private theorem upper_out {N j : ℕ} (b : ℕ → ℤ) (hj : N<j) : upperDivisor N b j=0 := by
  unfold upperDivisor
  exact sum_eq_zero fun i hi => if_neg (not_le.mpr ((mem_Icc.mp hi).2.trans_lt hj))

private theorem subsequence_norm {N : ℕ} (v : ℕ → ℝ) (hv : ∀ j, N<j → v j=0)
    (g : ℕ → ℕ) (hg : Function.Injective g) (hle : ∀ k, k≤g k) :
    conductorNorm N (fun k => v (g k)) ≤ conductorNorm N v := by
  let S := Icc 1 N
  let T := S.image g
  have him : ∑ k ∈ S, v (g k)^2 = ∑ j ∈ T, v j^2 :=
    (sum_image (fun _ _ _ _ he => hg he)).symm
  have he : ∑ j ∈ S, v j^2 = ∑ j ∈ T∪S, v j^2 := by
    apply sum_subset subset_union_right
    intro j hj hjs
    have hjt : j∈T := (mem_union.mp hj).resolve_right hjs
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hjt
    have hgpos := (mem_Icc.mp hk).1.trans (hle k)
    rw [hv _ (lt_of_not_ge fun h => hjs (mem_Icc.mpr ⟨hgpos,h⟩))]
    norm_num
  apply Real.sqrt_le_sqrt
  change (∑ k ∈ S, v (g k)^2) ≤ ∑ k ∈ S, v k^2
  rw [him,he]
  exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun _ _ _ => sq_nonneg _)

private theorem weighted_row {N : ℕ} (r w v : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hm : Monotone r) (hw : ∀ k, 0≤w k) (hv : ∀ j, N<j → v j=0)
    (g : ℕ → ℕ) (hg : Function.Injective g) (hle : ∀ k, k≤g k) :
    ∑ k ∈ Icc 1 N, w k*|v (g k)| ≤
      conductorNorm N (fun k => w k/r k)*conductorNorm N (fun j => r j*v j) := by
  let p := fun k => w k/r k
  let z := fun j => r j*|v j|
  have he (k : ℕ) : w k*|v (g k)| ≤ p k*z (g k) := by
    calc _ = p k*(r k*|v (g k)|) := by dsimp [p]; field_simp [(hr k).ne']
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (hm (hle k)) (abs_nonneg _)) (div_nonneg (hw k) (hr k).le)
  have hz : conductorNorm N z = conductorNorm N (fun j => r j*v j) := by
    simp only [conductorNorm,z,mul_pow,sq_abs]
  calc _ ≤ ∑ k ∈ Icc 1 N, p k*z (g k) := sum_le_sum fun k _ => he k
       _ ≤ conductorNorm N p*conductorNorm N (fun k => z (g k)) :=
         Real.sum_mul_le_sqrt_mul_sqrt _ _ _
       _ ≤ conductorNorm N p*conductorNorm N z :=
         mul_le_mul_of_nonneg_left (subsequence_norm z (fun j hj => by simp [z,hv j hj]) g hg hle)
           (Real.sqrt_nonneg _)
       _ = _ := by rw [hz]

private def contactMajorant (N s : ℕ) (u v w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc 1 N, w k * ∑ i ∈ Icc 1 N, |u i|*|v ((k+s)*i)|

private theorem contactMajorant_le (N s : ℕ) (r w u v : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hm : Monotone r) (hw : ∀ k, 0≤w k)
    (hu : ∀ j, N<j → u j=0) (hv : ∀ j, N<j → v j=0) :
    contactMajorant N s u v w ≤ conductorNorm N (fun k => 1/r k) *
      conductorNorm N (fun k => w k/r k) * conductorNorm N (fun i => r i*u i) *
      conductorNorm N (fun i => r i*v i) := by
  let S := Icc 1 N
  let V := conductorNorm N (fun i => r i*v i)
  let W := conductorNorm N (fun k => w k/r k)
  have hrow (i : ℕ) (hi : i∈S) : ∑ k ∈ S, w k*|v ((k+s)*i)| ≤ W*V := by
    have hip := (mem_Icc.mp hi).1
    apply weighted_row r w v hr hm hw hv _ (fun k j he => Nat.add_right_cancel
      (Nat.eq_of_mul_eq_mul_right hip he))
    exact fun k => (Nat.le_add_right k s).trans (Nat.le_mul_of_pos_right (k+s) hip)
  have h₁ := weighted_row (N := N) r (fun _ => 1) u hr hm (fun _ => zero_le_one) hu
    id Function.injective_id (fun _ => le_rfl)
  simp only [id_eq,one_mul] at h₁
  calc contactMajorant N s u v w = ∑ i ∈ S, |u i|*(∑ k ∈ S, w k*|v ((k+s)*i)|) := by
         simp only [contactMajorant,S,mul_sum]
         rw [sum_comm]
         refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
         ring
       _ ≤ (∑ i ∈ S, |u i|)*(W*V) := by
         rw [sum_mul]
         exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (abs_nonneg _)
       _ ≤ _ := by
         have hWV : 0≤W*V := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
         calc _ ≤ _ := mul_le_mul_of_nonneg_right h₁ hWV
              _ = _ := by dsimp [W,V]; ring

/-- Weighted variation of every positive quotient of the full mixed form.
All four directed terms use the same pair of individual conductor energies. -/
theorem twoSided_variation_separate (N : ℕ) (a b : ℕ → ℤ) (r w : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) (hw : ∀ k, 0≤w k) :
    let u := fun i => (upperDivisor N a i:ℝ)
    let v := fun i => (upperDivisor N b i:ℝ)
    ∑ k ∈ Icc 1 N, w k*|twoSidedCoefficient N a b k| ≤
      4*conductorNorm N (fun k => 1/r k)*conductorNorm N (fun k => w k/r k)*
        conductorNorm N (fun i => r i*u i)*conductorNorm N (fun i => r i*v i) := by
  intro u v
  let S := Icc 1 N
  let A (k : ℕ) (u v : ℕ → ℝ) := ∑ i ∈ S, |u i|*|v (k*i)|
  let T (k : ℕ) := ∑ i ∈ S, (u i*v (k*i)+v i*u (k*i))
  have hA (k : ℕ) : |T k| ≤ A k u v+A k v u := by
    rw [← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    simpa only [abs_mul] using abs_add_le (u i*v (k*i)) (v i*u (k*i))
  have hcell (k : ℕ) (hk : k∈S) :
      |twoSidedCoefficient N a b k| ≤ (A k u v+A k v u)+(A (k+1) u v+A (k+1) v u) := by
    change k ∈ Icc 1 N at hk
    have he : twoSidedCoefficient N a b k = T k-T (k+1) :=
      twoSidedCoefficient_difference (mem_Icc.mp hk).2 a b
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (hA _) (hA _))
  have hu : ∀ j, N<j → u j=0 := fun j hj => by simp [u,upper_out a hj]
  have hv : ∀ j, N<j → v j=0 := fun j hj => by simp [v,upper_out b hj]
  have hh := sum_le_sum (s := S) fun k hk => mul_le_mul_of_nonneg_left (hcell k hk) (hw k)
  simp only [mul_add,sum_add_distrib] at hh
  have h₀ := contactMajorant_le N 0 r w u v hr hm hw hu hv
  have h₁ := contactMajorant_le N 1 r w u v hr hm hw hu hv
  have h₂ := contactMajorant_le N 0 r w v u hr hm hw hv hu
  have h₃ := contactMajorant_le N 1 r w v u hr hm hw hv hu
  simp only [contactMajorant,Nat.add_zero] at h₀ h₁ h₂ h₃
  dsimp only [S,A] at hh
  linarith only [hh,h₀,h₁,h₂,h₃]

/-- On the entire integration interval, each real monomial is bounded by
one. The two independent weighted energies thus dominate the whole jet. -/
theorem mixedJetSection_separate {N : ℕ} (a b : ℕ → ℤ) (r : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    let u := fun i => (upperDivisor N a i:ℝ)
    let v := fun i => (upperDivisor N b i:ℝ)
    |mixedJetSection N a b x| ≤ 2*(conductorNorm N (fun k => 1/r k))^2 *
      conductorNorm N (fun i => r i*u i)*conductorNorm N (fun i => r i*v i) := by
  intro u v
  let S := Icc 1 N
  let J (m n : ℕ) := x^(max m n-min m n-1)+x^(m+n-1)
  have hj (m n : ℕ) : |J m n|≤2 := by
    dsimp only [J]
    rw [abs_of_nonneg (add_nonneg (pow_nonneg hx.1 _) (pow_nonneg hx.1 _))]
    linarith only [pow_le_one₀ (n := max m n-min m n-1) hx.1 hx.2,
      pow_le_one₀ (n := m+n-1) hx.1 hx.2]
  have hentry (m n : ℕ) : |u m*v n*J m n| ≤ |u m|*|v n|*2 := by
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_left (hj m n) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hnorm (c : ℕ → ℤ) : ∑ i ∈ S, |(upperDivisor N c i:ℝ)| ≤
      conductorNorm N (fun k => 1/r k)*conductorNorm N (fun i => r i*upperDivisor N c i) := by
    simpa only [one_mul,id_eq] using weighted_row (N := N) r (fun _ => 1)
      (fun i => (upperDivisor N c i:ℝ)) hr hm (fun _ => zero_le_one)
      (fun j hj => by simp [upper_out c hj]) id Function.injective_id (fun _ => le_rfl)
  change |∑ n ∈ S, ∑ m ∈ S.erase n, u m*v n*J m n| ≤ _
  calc _ ≤ ∑ n ∈ S, ∑ m ∈ S.erase n, |u m|*|v n|*2 := by
         apply (abs_sum_le_sum_abs _ _).trans
         exact sum_le_sum fun n _ => (abs_sum_le_sum_abs _ _).trans
           (sum_le_sum fun m _ => hentry m n)
       _ ≤ ∑ n ∈ S, ∑ m ∈ S, |u m|*|v n|*2 :=
         sum_le_sum fun n _ => sum_le_sum_of_subset_of_nonneg (erase_subset n S)
           (fun m _ _ => by positivity)
       _ = 2*((∑ i ∈ S, |u i|)*(∑ i ∈ S, |v i|)) := by
         simp only [← sum_mul,← mul_sum]
         ring
       _ ≤ 2*((conductorNorm N (fun k => 1/r k)*conductorNorm N (fun i => r i*u i))*
           (conductorNorm N (fun k => 1/r k)*conductorNorm N (fun i => r i*v i))) := by
         apply mul_le_mul_of_nonneg_left _ (by norm_num)
         exact mul_le_mul (hnorm a) (hnorm b) (sum_nonneg fun _ _ => abs_nonneg _)
           (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
       _ = _ := by ring

/-- Integrated joint estimate in the topology of the completed mixed Weil
form, with both divisors arbitrary. Only the two scalar weight norms carry
cutoff dependence outside the individual conductor energies. -/
theorem interleaved_joint_separate (N : ℕ) (a b : ℕ → ℤ) (r w : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) (hw : ∀ k, 0≤w k) :
    let A := conductorNorm N (fun k => 1/r k)
    let B := conductorNorm N (fun k => w k/r k)
    let U := conductorNorm N (fun i => r i*upperDivisor N a i)
    let V := conductorNorm N (fun i => r i*upperDivisor N b i)
    (∑ k ∈ Icc 1 N, w k*|twoSidedCoefficient N a b k|) +
      (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 ≤ (4*A*B+A^2)*U*V := by
  intro A B U V
  have hJ : Continuous (mixedJetSection N a b) := by
    change Continuous (fun x : ℝ => ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (upperDivisor N a m:ℝ)*upperDivisor N b n*(x^(max m n-min m n-1)+x^(m+n-1)))
    fun_prop
  have hi := intervalIntegral.integral_mono_on zero_le_one
    (hJ.abs.intervalIntegrable volume 0 1) (continuous_const.intervalIntegrable volume 0 1)
    (fun x hx => mixedJetSection_separate a b r hr hm hx)
  rw [intervalIntegral.integral_const] at hi
  simp only [sub_zero,one_smul] at hi
  have hv := twoSided_variation_separate N a b r w hr hm hw
  change (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|) ≤ 2*A^2*U*V at hi
  change _ ≤ 4*A*B*U*V at hv
  linarith only [hi,hv]

/-- A square-summable pair of scalar prices gives one separate-energy
constant for all interleavings and all cutoffs. -/
theorem interleaved_joint_uniform (r w : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hw : ∀ k, 0≤w k) (h₁ : Summable (fun k => (1/r k)^2))
    (h₂ : Summable (fun k => (w k/r k)^2)) :
    let A := Real.sqrt (∑' k, (1/r k)^2)
    let B := Real.sqrt (∑' k, (w k/r k)^2)
    ∀ (N : ℕ) (a b : ℕ → ℤ),
      (∑ k ∈ Icc 1 N, w k*|twoSidedCoefficient N a b k|) +
        (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 ≤
          (4*A*B+A^2)*conductorNorm N (fun i => r i*upperDivisor N a i)*
            conductorNorm N (fun i => r i*upperDivisor N b i) := by
  intro A B N a b
  have scalar (f : ℕ → ℝ) (hf : Summable (fun k => f k^2)) :
      conductorNorm N f ≤ Real.sqrt (∑' k, f k^2) :=
    Real.sqrt_le_sqrt (hf.sum_le_tsum _ (fun _ _ => sq_nonneg _))
  have hA := scalar _ h₁
  have hB := scalar _ h₂
  have hA₀ : 0≤conductorNorm N (fun k => 1/r k) := Real.sqrt_nonneg _
  have hB₀ : 0≤conductorNorm N (fun k => w k/r k) := Real.sqrt_nonneg _
  apply (interleaved_joint_separate N a b r w hr hm hw).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB hB₀
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) (pow_le_pow_left₀ hA₀ hA 2)

#print axioms twoSided_variation_separate
#print axioms mixedJetSection_separate
#print axioms interleaved_joint_separate
#print axioms interleaved_joint_uniform
end GaloisForLFunctions.SignedArithmeticCorrespondences
