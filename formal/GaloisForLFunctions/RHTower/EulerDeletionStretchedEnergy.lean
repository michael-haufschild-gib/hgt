import GaloisForLFunctions.RHTower.EulerDeletionQuotientHarmonicBound

/-!
# A stretched-exponential ceiling for the complete Möbius source

Cauchy condensation preserves half of the Mertens saving in the entire
harmonic tail. Optimizing the physical quotient depth preserves that same
saving in the full primitive energy, including every complementary cell.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionStretchedEnergy
open DeletionMobiusPrimitive

/-- Half of the exponent in the unconditional Mertens saving. -/
def saving (x : ℝ) : ℝ := Real.exp (-(Real.log x ^ ((1 : ℝ)/3)/216))

private theorem saving_pos (x : ℝ) : 0 < saving x := Real.exp_pos _

private theorem saving_le_one {x : ℝ} (hx : 1 ≤ x) : saving x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := Real.rpow_nonneg (Real.log_nonneg hx) ((1 : ℝ)/3)
  linarith

private theorem saving_anti {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    saving y ≤ saving x := by
  apply Real.exp_le_exp.mpr
  have h := Real.rpow_le_rpow (Real.log_nonneg hx)
    (Real.log_le_log (by linarith) hxy) (show (0 : ℝ) ≤ 1/3 by norm_num)
  linarith

private theorem saving_sq (x : ℝ) : saving x^2=deningerMertensSaving x := by
  rw [pow_two, saving, ← Real.exp_add, deningerMertensSaving]
  congr 1
  ring_nf

private def ray (n : ℕ) : ℝ := saving n/(n : ℝ)

private theorem ray_nonneg (n : ℕ) : 0 ≤ ray n :=
  div_nonneg (saving_pos _).le (Nat.cast_nonneg _)

private theorem ray_summable : Summable ray := by
  have hanti ⦃m n : ℕ⦄ (hm : 0 < m) (hmn : m ≤ n) : ray n ≤ ray m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hm.trans_le hmn)
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact (div_le_div_of_nonneg_right (saving_anti hm1 hmnR) hn0.le).trans
      (div_le_div_of_nonneg_left (saving_pos _).le hm0 hmnR)
  rw [← summable_condensed_iff_of_nonneg ray_nonneg hanti]
  let c : ℝ := Real.log 2 ^ ((1 : ℝ)/3)/216
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  apply (deningerCubeRootExp_summable hc).congr
  intro k
  have hk : (0 : ℝ) < (2 : ℝ)^k := by positivity
  simp only [ray, saving, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow, Real.mul_rpow (Nat.cast_nonneg k) hlog2.le,
    mul_div_assoc, mul_div_cancel₀ _ hk.ne']
  congr 1
  dsimp [c]
  ring_nf

private theorem saving_tendsto : Tendsto (fun N : ℕ => saving N) atTop (nhds 0) := by
  have hu : Tendsto (fun N : ℕ => Real.log (N : ℝ)^((1 : ℝ)/3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  unfold saving
  have h := tendsto_neg_atTop_atBot.comp (hu.atTop_div_const (by norm_num : (0 : ℝ) < 216))
  exact Real.tendsto_exp_atBot.comp h

/-- The actual harmonic Möbius partial sum retains a stretched-exponential saving. -/
theorem harmonic_rate : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    |deningerHarmonicPartial N| ≤ C*saving N := by
  obtain ⟨B,hB,hrate⟩ := deningerMertensM_rate
  obtain ⟨K,hK⟩ := eventually_atTop.mp hrate
  let T : ℝ := ∑' n : ℕ, ray n
  have hT : 0 ≤ T := tsum_nonneg ray_nonneg
  refine ⟨B*(1+T),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1] with N hNK hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hM (k : ℕ) (hk : N ≤ k) : |Sieve.mertensM k| ≤ B*(k : ℝ)*saving k^2 := by
    rw [saving_sq]
    exact hK k (hNK.trans hk)
  have hboundary : |Sieve.mertensM N/(N : ℝ)| ≤ B*saving N := by
    rw [abs_div,abs_of_pos hN0]
    apply (div_le_iff₀ hN0).mpr
    calc _  ≤  B*(N : ℝ)*saving N^2 := hM N le_rfl
         _  ≤  (B*saving N)*(N : ℝ) := by
           have h := mul_le_mul_of_nonneg_left (saving_le_one hN1) (saving_pos (N : ℝ)).le
           nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hB hN0.le)]
  let f (i : ℕ) : ℝ := Sieve.mertensM (i+N)/
    (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))
  have hf : Summable f := (summable_nat_add_iff N).mpr deningerMertensHarmonic_summable
  have hterm (i : ℕ) : |f i| ≤ (B*saving N)*ray (i+N) := by
    have hkN : N ≤ i+N := Nat.le_add_left _ _
    have hk0 : (0 : ℝ) < (i+N : ℕ) := by positivity
    have hmono := saving_anti hN1 (show (N : ℝ) ≤ (i+N : ℕ) by exact_mod_cast hkN)
    dsimp [f,ray]
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ) < ((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))).mpr
    have hm := hM (i+N) hkN
    have hs : saving ((i+N : ℕ) : ℝ)^2 ≤ saving N*saving ((i+N : ℕ) : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hmono (saving_pos ((i+N : ℕ) : ℝ)).le]
    have hbnd := mul_le_mul_of_nonneg_left hs (show 0 ≤ B*((i+N : ℕ) : ℝ) by positivity)
    have heq : B*saving N*(saving ((i+N : ℕ) : ℝ)/((i+N : ℕ) : ℝ))*
        (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1)) =
        B*saving N*saving ((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1) := by field_simp
    rw [heq]
    nlinarith [mul_nonneg hB (mul_nonneg (saving_pos (N : ℝ)).le (saving_pos ((i+N : ℕ) : ℝ)).le)]
  have htailRay : (∑' i : ℕ, ray (i+N)) ≤ T := by
    have he := ray_summable.sum_add_tsum_nat_add N
    have hn : 0 ≤ ∑ i∈Finset.range N, ray i := Finset.sum_nonneg (fun i _ => ray_nonneg i)
    dsimp [T]
    linarith
  have htail : |∑' i : ℕ, f i| ≤ B*saving N*T := by
    calc _  ≤  ∑' i : ℕ, |f i| := by
           simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
         _  ≤  ∑' i : ℕ, (B*saving N)*ray (i+N) :=
           hf.abs.tsum_le_tsum hterm (((summable_nat_add_iff N).mpr ray_summable).mul_left _)
         _ = (B*saving N)*(∑' i : ℕ, ray (i+N)) := tsum_mul_left
         _  ≤  B*saving N*T := mul_le_mul_of_nonneg_left htailRay (mul_nonneg hB (saving_pos _).le)
  rw [Sieve.deningerHarmonicPartial_eq_mertens_boundary_sub_tail]
  exact (abs_sub _ _).trans (by change |Sieve.mertensM N/(N : ℝ)|+|∑' i, f i| ≤ _; nlinarith)



/-- The complete physical primitive energy retains a stretched-exponential saving. -/
theorem primitiveEnergy_rate : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    primitiveEnergy N ≤ C*(N : ℝ)*saving N := by
  obtain ⟨A,hA,hH⟩ := harmonic_rate
  obtain ⟨B,hB,hE⟩ := DeletionQuotientTail.exists_primitiveEnergy_uniform_log_depth_bound
  let D : ℝ := A+3*B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsmall : ∀ᶠ N : ℕ in atTop, saving N ≤ 1/2 := by
    filter_upwards [saving_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))] with N hN
    exact hN.le
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨6+2*D^2,by positivity,?_⟩
  filter_upwards [hH,hE,hsmall,hlog,eventually_ge_atTop 1] with N hHN hEN hsN hlogN hN
  let s : ℝ := saving N
  let t : ℝ := Real.log (N : ℝ)^((1 : ℝ)/3)/216
  let P : ℝ := Real.exp t
  let L : ℕ := ⌊P⌋₊
  have hs : 0 < s := saving_pos _
  have hs1 : s ≤ 1 := saving_le_one (by exact_mod_cast hN)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hP : 0 < P := Real.exp_pos _
  have hPs : P*s=1 := by
    dsimp [P,s,saving,t]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hP2 : 2 ≤ P := by
    change s ≤ 1/2 at hsN
    nlinarith [mul_le_mul_of_nonneg_left hsN hP.le]
  have hLP : (L : ℝ) ≤ P := Nat.floor_le hP.le
  have hPL : P < (L : ℝ)+1 := Nat.lt_floor_add_one P
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hhalf : P/2 ≤ (L : ℝ) := by linarith
  have hlogL : Real.log (L : ℝ) ≤ t := by
    calc _  ≤  Real.log P := Real.log_le_log hL0 hLP
         _ = t := Real.log_exp t
  have htP : t ≤ P := by linarith [Real.add_one_le_exp t]
  have hts : t*s ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right htP hs.le]
  have hcost : s^2*(2+Real.log (L : ℝ)) ≤ 3*s := by
    have h1 := mul_le_mul_of_nonneg_left hlogL (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left hs1 hs.le
    have h3 := mul_le_mul_of_nonneg_left hts hs.le
    nlinarith
  let b : ℝ := |deningerHarmonicPartial N|+B*s^2*(2+Real.log (L : ℝ))
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbD : b ≤ D*s := by
    have h := mul_le_mul_of_nonneg_left hcost hB
    dsimp [b,D]
    change |deningerHarmonicPartial N| ≤ A*s at hHN
    nlinarith
  have henergy := hEN L hL1
  rw [← saving_sq] at henergy
  change primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*b^2+(N : ℝ)/(L : ℝ) at henergy
  have hhead : 2*(N : ℝ)*(L : ℝ)*b^2 ≤ 2*D^2*(N : ℝ)*s := by
    have hsq := pow_le_pow_left₀ hb hbD 2
    calc _ = (2*(N : ℝ))*((L : ℝ)*b^2) := by ring_nf
         _  ≤  (2*(N : ℝ))*(P*(D*s)^2) :=
           mul_le_mul_of_nonneg_left (mul_le_mul hLP hsq (sq_nonneg b) hP.le) (by positivity)
         _ = 2*D^2*(N : ℝ)*(P*s)*s := by ring_nf
         _ = _ := by rw [hPs]; ring
  have htail : (N : ℝ)/(L : ℝ) ≤ 2*(N : ℝ)*s := by
    apply (div_le_iff₀ hL0).mpr
    have hh := mul_le_mul_of_nonneg_right hhalf hs.le
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : Real.log (N : ℝ)^((1 : ℝ)/3) ≤ Real.log (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlogN (show (1 : ℝ)/3 ≤ 1 by norm_num)
  have htlog : t ≤ Real.log (N : ℝ) := by dsimp [t]; linarith
  have hPN : P ≤ (N : ℝ) := by
    calc _  ≤  Real.exp (Real.log (N : ℝ)) := Real.exp_le_exp.mpr htlog
         _ = _ := Real.exp_log hN0
  have hNs : 1 ≤ (N : ℝ)*s := by nlinarith [mul_le_mul_of_nonneg_right hPN hs.le]
  calc _  ≤  4+2*(N : ℝ)*(L : ℝ)*b^2+(N : ℝ)/(L : ℝ) := henergy
       _  ≤  4*(N : ℝ)*s+2*D^2*(N : ℝ)*s+2*(N : ℝ)*s := by linarith
       _ = _ := by dsimp [s]; ring_nf

/-- The actual modular Hilbert source inherits the full stretched-exponential ceiling. -/
theorem modular_norm_sq_rate : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    ‖bdMobiusModularApproximantVec N‖^2 ≤ C*(N : ℝ)*saving N := by
  obtain ⟨C,hC,h⟩ := primitiveEnergy_rate
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with N hN
  exact (DeletionMobiusGlobal.modular_norm_sq_le_primitiveEnergy N).trans hN



/-- A single cutoff and constant control every logarithmic order of the actual full energy. -/
theorem primitiveEnergy_factorial_rate : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
    primitiveEnergy N*Real.log (N : ℝ)^q ≤
      C*(N : ℝ)*216^(3*q)*((3*q).factorial : ℝ) := by
  obtain ⟨C,hC,hE⟩ := primitiveEnergy_rate
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,eventually_ge_atTop 1] with N hEN hN
  intro q
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  let t : ℝ := Real.log (N : ℝ)^((1 : ℝ)/3)/216
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcube : (Real.log (N : ℝ)^((1 : ℝ)/3))^3=Real.log (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    norm_num
  have hp : t^(3*q)=Real.log (N : ℝ)^q/216^(3*q) := by
    dsimp [t]
    rw [div_pow,pow_mul,hcube]
  have hs := Real.pow_div_factorial_le_exp t ht (3*q)
  rw [hp] at hs
  have hf : (0 : ℝ) < (3*q).factorial := by positivity
  have hpow : (0 : ℝ) < 216^(3*q) := by positivity
  have hpoly : Real.log (N : ℝ)^q ≤
      (216^(3*q)*((3*q).factorial : ℝ))*Real.exp t := by
    have hd : Real.log (N : ℝ)^q/(216^(3*q)*((3*q).factorial : ℝ)) ≤ Real.exp t := by
      simpa only [div_div] using hs
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hpow hf)).mp hd
  have hexp : saving N*Real.exp t=1 := by
    dsimp [saving,t]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  calc _ ≤ (C*(N : ℝ)*saving N)*Real.log (N : ℝ)^q :=
         mul_le_mul_of_nonneg_right hEN (pow_nonneg hlog q)
       _ ≤ (C*(N : ℝ)*saving N)*
           ((216^(3*q)*((3*q).factorial : ℝ))*Real.exp t) :=
         mul_le_mul_of_nonneg_left hpoly (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg N)) (saving_pos _).le)
       _ = C*(N : ℝ)*216^(3*q)*((3*q).factorial : ℝ)*(saving N*Real.exp t) := by ring_nf
       _ = _ := by rw [hexp,mul_one]

end RHTower.DeletionStretchedEnergy
