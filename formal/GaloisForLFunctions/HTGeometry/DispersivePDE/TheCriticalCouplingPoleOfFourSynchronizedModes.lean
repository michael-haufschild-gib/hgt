import GaloisForLFunctions.HTGeometry.DispersivePDE.HowFourSynchronizedAmplitudesMoveWithTheCoupling

/-!
# The pole at the geometric-mean coupling

Each positive amplitude equation has a normalized factor exceeding one.
Their product is exactly the product of the four self-couplings divided
by the fourth power of the interaction. As the interaction reaches its
threshold, all four factors converge to one. Telescoping their product
recovers the coefficient of the diverging squared amplitude.
-/

open Filter Topology
noncomputable section
namespace HTGeometry.CriticalQuartet

/-- Geometric mean of the four self-couplings. -/
def criticalCoupling (μ : Fin 4 → ℝ) : ℝ := Real.sqrt (Real.sqrt (product μ))

private theorem critical_pos {μ : Fin 4 → ℝ} (hμ : ∀ i,0<μ i) : 0<criticalCoupling μ :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (product_pos hμ))

private theorem critical_fourth {μ : Fin 4 → ℝ} (hμ : ∀ i,0<μ i) : (criticalCoupling μ)^4=product μ := by
  unfold criticalCoupling
  rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt (product_pos hμ).le]

private def gain (μ : Fin 4 → ℝ) (b : ℝ) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  μ i*x i^4/(b*product x)

private def normalized (b : ℝ) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  x i^2/Real.sqrt (b*product x)

private theorem product_div_const (v : Fin 4 → ℝ) (q : ℝ) :
    product (fun i => v i/q)=product v/q^4 := by
  unfold product
  rw [div_mul_div_comm,div_mul_div_comm,div_mul_div_comm,show q*q*q*q=q^4 by ring]

private theorem gain_product {μ x : Fin 4 → ℝ} (b : ℝ) (hx : ∀ i,0<x i) :
    product (gain μ b x)=product μ/b^4 := by
  change product (fun i => (μ i*x i^4)/(b*product x))=_
  rw [product_div_const,product_mul μ (fun i => x i^4),product_fourth x,mul_pow]
  rw [mul_comm (product μ) ((product x)^4),mul_comm (b^4) ((product x)^4)]
  exact mul_div_mul_left _ _ (pow_ne_zero 4 (product_pos hx).ne')

private theorem gain_normalized {μ x : Fin 4 → ℝ} {b : ℝ} (hb : 0<b) (hx : ∀ i,0<x i) (i : Fin 4) :
    gain μ b x i=μ i*(normalized b x i)^2 := by
  unfold gain normalized
  rw [div_pow,Real.sq_sqrt (mul_pos hb (product_pos hx)).le]
  ring

private theorem gain_increment {μ x : Fin 4 → ℝ} {m b : ℝ} (hb : 0<b)
    (hx : Synchronized μ m b x) (i : Fin 4) :
    gain μ b x i=1+(m/Real.sqrt (b*product x))*normalized b x i := by
  have L := mul_pos hb (product_pos hx.1)
  unfold gain normalized
  rw [hx.2 i,add_div,div_self L.ne',div_mul_div_comm,←sq,Real.sq_sqrt L.le,add_comm]

private theorem factor_bound {A : Fin 4 → ℝ} (h : ∀ i, 1≤A i) (i : Fin 4) : A i≤product A := by
  calc A i = ∏ j : Fin 4, (if j=i then A j else 1) := by simp
       _ ≤ ∏ j : Fin 4, A j := by
         apply Finset.prod_le_prod
         · intro j _
           split <;> first | exact zero_le_one.trans (h j) | exact zero_le_one
         · intro j _
           split <;> first | exact le_rfl | exact h j
       _ = _ := Fin.prod_univ_four _

private def incrementSum (A z : Fin 4 → ℝ) : ℝ :=
  z 0+A 0*z 1+A 0*A 1*z 2+A 0*A 1*A 2*z 3

private theorem product_increments (A z : Fin 4 → ℝ) (t : ℝ) (h : ∀ i,A i=1+t*z i) :
    product A-1=t*incrementSum A z := by
  have tel : product A-1=(A 0-1)+A 0*(A 1-1)+A 0*A 1*(A 2-1)+A 0*A 1*A 2*(A 3-1) := by
    unfold product
    ring
  have step (i : Fin 4) : A i-1=t*z i := by rw [h]; ring
  rw [tel,step,step,step,step]
  unfold incrementSum
  ring

private theorem finite_residue {μ x : Fin 4 → ℝ} {m b : ℝ} (hb : 0<b) (hx : Synchronized μ m b x)
    (i : Fin 4) :
    (product μ-b^4)*x i^2=m*b^4*normalized b x i*incrementSum (gain μ b x) (normalized b x) := by
  have prod := (eq_div_iff (pow_ne_zero 4 hb.ne')).mp (gain_product (μ:=μ) b hx.1)
  have gap : product μ-b^4=b^4*(product (gain μ b x)-1) := by linarith only [prod]
  have inc := product_increments _ _ _ (gain_increment hb hx)
  rw [gap,inc]
  dsimp only [normalized]
  ring

/-- Residue in the determinant variable. The normalized mode gains
all tend to one, and the four reciprocal square roots of the couplings
enter through their sum. -/
theorem determinant_amplitude_residue {α : Type*} {F : Filter α} {μ : Fin 4 → ℝ} {m : ℝ}
    (hμ : ∀ i,0<μ i) (hm : 0<m) (b : α → SubcriticalCoupling μ)
    (hb : Tendsto (fun n => (b n:ℝ)^4) F (𝓝 (product μ))) (i : Fin 4) :
    Tendsto (fun n => (product μ-(b n:ℝ)^4)*(groundAmplitude hμ hm (b n) i)^2) F
      (𝓝 (m*product μ*(1/Real.sqrt (μ i))*total (fun j => 1/Real.sqrt (μ j)))) := by
  let x n := groundAmplitude hμ hm (b n)
  let A n := gain μ (b n) (x n)
  let z n := normalized (b n) (x n)
  let r (j : Fin 4) := 1/Real.sqrt (μ j)
  have hs n : Synchronized μ m (b n) (x n) := groundAmplitude_synchronized hμ hm (b n)
  have zn n j : 0≤z n j := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have lo n j : 1≤A n j := by
    change 1≤gain μ (b n) (x n) j
    rw [gain_increment (b n).2.1 (hs n)]
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hm.le (Real.sqrt_nonneg _)) (zn n j))
  have top n j : A n j≤product μ/(b n:ℝ)^4 := (factor_bound (lo n) j).trans_eq
    (gain_product (μ:=μ) (b n) (hs n).1)
  have hp := product_pos hμ
  have cap : Tendsto (fun n => product μ/(b n:ℝ)^4) F (𝓝 1) := by
    have bound := (tendsto_const_nhds (x:=product μ)).div hb hp.ne'
    change Tendsto (fun n => product μ/(b n:ℝ)^4) F (𝓝 (product μ/product μ)) at bound
    rwa [div_self hp.ne'] at bound
  have ha (j : Fin 4) : Tendsto (fun n => A n j) F (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cap (fun n => lo n j) (fun n => top n j)
  have nz (j : Fin 4) : Tendsto (fun n => z n j) F (𝓝 (r j)) := by
    have eq (n : α) : z n j=Real.sqrt (A n j/μ j) := by
      have id : A n j/μ j=(z n j)^2 := by
        apply (div_eq_iff (hμ j).ne').mpr
        exact (gain_normalized (μ:=μ) (b n).2.1 (hs n).1 j).trans (mul_comm ..)
      rw [id,Real.sqrt_sq (zn n j)]
    simp_rw [eq]
    have lim := (Real.continuous_sqrt.tendsto (1/μ j)).comp ((ha j).div_const (μ j))
    simpa only [Function.comp_def,Real.sqrt_div zero_le_one,Real.sqrt_one,r] using lim
  have sumlim : Tendsto (fun n => incrementSum (A n) (z n)) F (𝓝 (total r)) := by
    have lim := (((nz 0).add ((ha 0).mul (nz 1))).add (((ha 0).mul (ha 1)).mul (nz 2))).add
      ((((ha 0).mul (ha 1)).mul (ha 2)).mul (nz 3))
    simpa only [incrementSum,total,one_mul] using lim
  have p := (((tendsto_const_nhds (x:=m)).mul hb).mul (nz i)).mul sumlim
  have eq (n : α) : (product μ-(b n:ℝ)^4)*x n i^2=m*(b n:ℝ)^4*z n i*incrementSum (A n) (z n) :=
    finite_residue (b n).2.1 (hs n) i
  change Tendsto (fun n => (product μ-(b n:ℝ)^4)*x n i^2) F (𝓝 (m*product μ*r i*total r))
  simp_rw [eq]
  exact p

private theorem sum_scaled_limits {α : Type*} {F : Filter α} (q : α → ℝ) (x : α → Fin 4 → ℝ)
    (k : ℝ) (r : Fin 4 → ℝ)
    (h : ∀ i, Tendsto (fun n => q n*x n i^2) F (𝓝 (k*r i*total r))) :
    Tendsto (fun n => q n*total (fun i => x n i^2)) F (𝓝 (k*(total r)^2)) := by
  have lim := (((h 0).add (h 1)).add (h 2)).add (h 3)
  have src (n : α) : q n*x n 0^2+q n*x n 1^2+q n*x n 2^2+q n*x n 3^2 =
      q n*total (fun i => x n i^2) := by unfold total; ring
  have dst : k*r 0*total r+k*r 1*total r+k*r 2*total r+k*r 3*total r=k*(total r)^2 := by
    unfold total
    ring
  simp only [src,dst] at lim
  exact lim

/-- The limiting fraction of total squared amplitude carried by each
mode is its inverse square-root coupling divided by the sum of all four. -/
theorem critical_mass_shares {α : Type*} {F : Filter α} {μ : Fin 4 → ℝ} {m : ℝ}
    (hμ : ∀ i,0<μ i) (hm : 0<m) (b : α → SubcriticalCoupling μ)
    (hb : Tendsto (fun n => (b n:ℝ)^4) F (𝓝 (product μ))) (i : Fin 4) :
    Tendsto (fun n => let x := groundAmplitude hμ hm (b n)
      x i^2/total (fun j => x j^2)) F
      (𝓝 ((1/Real.sqrt (μ i))/total (fun j => 1/Real.sqrt (μ j)))) := by
  let x n := groundAmplitude hμ hm (b n)
  let r (j : Fin 4) := 1/Real.sqrt (μ j)
  let q n := product μ-(b n:ℝ)^4
  let k := m*product μ
  have lim i : Tendsto (fun n => q n*x n i^2) F (𝓝 (k*r i*total r)) :=
    determinant_amplitude_residue hμ hm b hb i
  have pr j : 0<r j := one_div_pos.mpr (Real.sqrt_pos.mpr (hμ j))
  have ps : 0<total r := (pr 0).trans_le (le_total (fun j => (pr j).le) 0)
  have pk : 0<k := mul_pos hm (product_pos hμ)
  have qlim := (lim i).div (sum_scaled_limits q x k r lim) (mul_pos pk (sq_pos_of_pos ps)).ne'
  change Tendsto (fun n => (q n*x n i^2)/(q n*total (fun j => x n j^2))) F
    (𝓝 (k*r i*total r/(k*(total r)^2))) at qlim
  have cancel (n : α) : (q n*x n i^2)/(q n*total (fun j => x n j^2))=x n i^2/total (fun j => x n j^2) :=
    mul_div_mul_left _ _ (sub_pos.mpr (b n).2.2).ne'
  have limit : k*r i*total r/(k*total r^2)=r i/total r := by field_simp [pk.ne',ps.ne']
  simp only [cancel,limit] at qlim
  exact qlim

/-- At the geometric mean B, the pole in the physical coupling B−b
has residue m B times the indicated inverse-root weights divided by four. -/
theorem critical_amplitude_residue {α : Type*} {F : Filter α} {μ : Fin 4 → ℝ} {m : ℝ}
    (hμ : ∀ i,0<μ i) (hm : 0<m) (b : α → SubcriticalCoupling μ)
    (hb : Tendsto (fun n => (b n:ℝ)) F (𝓝 (criticalCoupling μ))) (i : Fin 4) :
    Tendsto (fun n => (criticalCoupling μ-(b n:ℝ))*(groundAmplitude hμ hm (b n) i)^2) F
      (𝓝 (m*criticalCoupling μ/4*(1/Real.sqrt (μ i))*total (fun j => 1/Real.sqrt (μ j)))) := by
  let B := criticalCoupling μ
  have hB : 0<B := critical_pos hμ
  have top : B^4=product μ := critical_fourth hμ
  let R := (1/Real.sqrt (μ i))*total (fun j => 1/Real.sqrt (μ j))
  let q (s : ℝ) := B^3+B^2*s+B*s^2+s^3
  have fact (s : ℝ) : (B-s)*q s=B^4-s^4 := by unfold q; ring
  have qpos {s : ℝ} (hs : 0<s) : 0<q s := by unfold q; positivity
  have qlim : Tendsto (fun n => q (b n)) F (𝓝 (q B)) := by
    have cont : Continuous q := by unfold q; fun_prop
    exact (cont.tendsto B).comp hb
  have h₄ : Tendsto (fun n => (b n:ℝ)^4) F (𝓝 (product μ)) := by
    have raw : Tendsto (fun n => (b n:ℝ)^4) F (𝓝 (B^4)) := hb.pow 4
    simpa only [top] using raw
  have res := determinant_amplitude_residue hμ hm b h₄ i
  let x n := groundAmplitude hμ hm (b n) i
  have eq (n : α) : ((product μ-(b n:ℝ)^4)*x n^2)/q (b n)=(B-b n)*x n^2 := by
    apply (div_eq_iff (qpos (b n).2.1).ne').mpr
    have id := fact (b n)
    rw [top] at id
    rw [←id]
    ring
  have value : (m*product μ*(1/Real.sqrt (μ i))*total (fun j => 1/Real.sqrt (μ j)))/q B=m*B/4*R := by
    rw [←top]
    dsimp only [R,q]
    field_simp [hB.ne']
    ring
  have lim := res.div qlim (qpos hB).ne'
  change Tendsto (fun n => ((product μ-(b n:ℝ)^4)*x n^2)/q (b n)) F _ at lim
  simp only [eq,value] at lim
  simpa only [x,B,R,mul_assoc] using lim

/-- The minimum energy has a negative simple pole. Its residue involves
the square of the sum of the reciprocal square-root couplings. -/
theorem critical_minimum_energy_residue {α : Type*} {F : Filter α} {μ : Fin 4 → ℝ} {m : ℝ}
    (hμ : ∀ i,0<μ i) (hm : 0<m) (b : α → SubcriticalCoupling μ)
    (hb : Tendsto (fun n => (b n:ℝ)) F (𝓝 (criticalCoupling μ))) :
    Tendsto (fun n => (criticalCoupling μ-(b n:ℝ))*energy μ m (b n) (groundAmplitude hμ hm (b n))) F
      (𝓝 (-(m^2*criticalCoupling μ/4)*(total (fun j => 1/Real.sqrt (μ j)))^2)) := by
  let B := criticalCoupling μ
  let x n := groundAmplitude hμ hm (b n)
  let r (j : Fin 4) := 1/Real.sqrt (μ j)
  have mass := sum_scaled_limits (fun n => B-(b n:ℝ)) x (m*B/4) r (critical_amplitude_residue hμ hm b hb)
  have src (n : α) : -m*((B-(b n:ℝ))*total (fun i => x n i^2))=
      (B-(b n:ℝ))*energy μ m (b n) (x n) := by
    rw [energy_at_solution (groundAmplitude_synchronized hμ hm (b n))]
    ring
  have dst : -m*(m*B/4*(total r)^2)= -(m^2*B/4)*(total r)^2 := by ring
  have lim := (tendsto_const_nhds (x:= -m)).mul mass
  simp only [src,dst] at lim
  exact lim

#print axioms determinant_amplitude_residue
#print axioms critical_amplitude_residue
#print axioms critical_mass_shares
#print axioms critical_minimum_energy_residue
end HTGeometry.CriticalQuartet
