import GaloisForLFunctions.RHTower.MobiusDivisorEvenCorePrimeReserve

/-!
# Uniform pair-energy profile across the full prime-ratio ray

The physical renewal identity controls the complete first-prime term,
the second-prime remainder and both density changes. After normalization
by the smaller prime, the actual two-merger coefficient differs from
the original source evaluated at the prime ratio by at most C/sqrt(p),
uniformly for every q>=p. The original core remains fixed.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private def profileDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1)
private def profileEnergy (P : Finset ℕ) : ℝ := ∑'n,mobiusDivisorFixedCoreBlockMass P n

private lemma density_pos (P : Finset ℕ) (hP : ∀p∈P,p.Prime) : 0<profileDensity P := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]
    positivity
  · apply Finset.prod_pos
    intro p hp
    exact div_pos (by exact_mod_cast (hP p hp).pos) (by positivity)

private lemma density_insert (P : Finset ℕ) {p : ℕ} (hpP : p∉P) :
    profileDensity (insert p P)=(p:ℝ)/(p+1)*profileDensity P := by
  simp only [profileDensity,prod_insert hpP]
  ring

private lemma release_sqrt (P : Finset ℕ) (hP : ∀r∈P,r.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    profileEnergy P-profileEnergy (insert p P)=
      2*profileDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2)*mobiusDivisorDilationMean P p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr : (p:ℝ)^(-(3/2:ℝ))=Real.sqrt p/(p:ℝ)^2 := by
    rw [show -(3/2:ℝ)=1/2-2 by norm_num,Real.rpow_sub hpR,
      ← Real.sqrt_eq_rpow,Real.rpow_two]
  simpa only [profileEnergy,profileDensity,hr] using
    mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hP hp hpP

private lemma sqrt_kernel {x : ℝ} (hx : 0<x) :
    Real.sqrt x/x^2=1/(x*Real.sqrt x) := by
  have hs : Real.sqrt x≠0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

private lemma scaled_kernel_le {p q : ℝ} (hp : 0<p) (hpq : p≤q) :
    p*Real.sqrt q/q^2≤1/Real.sqrt p := by
  have hq : 0<q := hp.trans_le hpq
  have hden : p*Real.sqrt p≤q*Real.sqrt q :=
    mul_le_mul hpq (Real.sqrt_le_sqrt hpq) (Real.sqrt_nonneg p) hq.le
  have h := one_div_le_one_div_of_le (mul_pos hp (Real.sqrt_pos.mpr hp)) hden
  rw [← sqrt_kernel hp,← sqrt_kernel hq] at h
  have hm := mul_le_mul_of_nonneg_left h hp.le
  calc
    _ ≤ p*(Real.sqrt p/p^2) := by simpa [mul_div_assoc] using hm
    _ = _ := by rw [sqrt_kernel hp]; field_simp

private lemma ratio_factor {p q : ℝ} (hp : 0<p) (hq : 0<q) :
    p*Real.sqrt p*Real.sqrt q/q^2=(p/q)*Real.sqrt (p/q) := by
  rw [Real.sqrt_div hp.le]
  have hs : Real.sqrt q≠0 := (Real.sqrt_pos.mpr hq).ne'
  field_simp
  nlinarith [Real.sq_sqrt hq.le]

private lemma density_bounds (P : Finset ℕ) (hP : ∀r∈P,r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpP : p∉P)
    (hqi : q∉insert p P) (hpq : p≤q) :
    profileDensity (insert p P)≤profileDensity P ∧
    profileDensity (insert q (insert p P))≤profileDensity P ∧
    profileDensity P-profileDensity (insert q (insert p P))≤2*profileDensity P/(p:ℝ) := by
  have hρ := (density_pos P hP).le
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hpfrac : (p:ℝ)/(p+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hqfrac : (q:ℝ)/(q+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  rw [density_insert _ hqi,density_insert _ hpP]
  have ha := mul_le_mul_of_nonneg_right hpfrac hρ
  have hb := mul_le_mul_of_nonneg_right hqfrac
    (show 0≤(p:ℝ)/(p+1)*profileDensity P by positivity)
  simp only [one_mul] at ha hb
  refine ⟨ha,hb.trans ha,?_⟩
  have hcoef : 1-(q:ℝ)/(q+1)*((p:ℝ)/(p+1))≤2/(p:ℝ) := by
    field_simp
    nlinarith [mul_nonneg hpR.le (sub_nonneg.mpr hpqR)]
  have hm := mul_le_mul_of_nonneg_right hcoef hρ
  convert! hm using 1 <;> ring

/-- Uniform actual pair-energy profile at every prime ratio q/p>=1.
The error retains the complete first merger and both density changes. -/
theorem exists_bound_mobiusDivisorPrime_pair_ratio_profile (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃C : ℝ,0≤C ∧ ∀p q : ℕ,p.Prime → q.Prime → p∉P → q∉P → q≠p → p≤q →
      |(p:ℝ)*((∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
          ∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        2*(Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1))*
          ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*mobiusDivisorDilationMean P ((q:ℝ)/p)|≤
        C/Real.sqrt p := by
  obtain ⟨B,hB,hbound⟩ := exists_bound_mobiusDivisorDilationMean P hP hprime
  obtain ⟨D,hD,herror⟩ := exists_bound_mobiusDivisorDilationMean_insert_ratio P hP hprime
  have hρ := density_pos P hprime
  refine ⟨2*profileDensity P*(3*B+D),by positivity,?_⟩
  intro p q hp hq hpP hqP hqp hpq
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq.one_lt.le
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hqi : q∉insert p P := by simp [hqp,hqP]
  have hiprime : ∀r∈insert p P,r.Prime := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    · exact hprime r hr
  have hρp := density_pos (insert p P) hiprime
  have hρpq := density_pos (insert q (insert p P)) (by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    · exact hiprime r hr)
  obtain ⟨hρple,hρpqle,hρdiff⟩ := density_bounds P hprime hp hq hpP hqi hpq
  let t := Real.sqrt p
  let k := (p:ℝ)*Real.sqrt q/(q:ℝ)^2
  let z := mobiusDivisorDilationMean P ((q:ℝ)/p)
  let e := mobiusDivisorDilationMean (insert p P) q+t*z
  have ht : 0<t := Real.sqrt_pos.mpr hpR
  have hk : 0≤k := by dsimp [k]; positivity
  have hkle : k≤1/t := scaled_kernel_le hpR hpqR
  have ht2 : t^2=(p:ℝ) := Real.sq_sqrt hpR.le
  have hts : t≤(p:ℝ) := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hpR.le,Real.sqrt_nonneg (p:ℝ)]
  have htkin : t*k≤1 := by
    have hm := mul_le_mul_of_nonneg_left hkle ht.le
    have he : t*(1/t)=1 := by field_simp
    rwa [he] at hm
  have hz : |z|≤B := hbound _ ((le_div_iff₀ hpR).mpr (by simpa using hpqR))
  have he : |e|≤D := herror p hp hpP q hq1
  have hwp := hbound p hp1
  have hrp := release_sqrt P hprime hp hpP
  have hrq := release_sqrt (insert p P) hiprime hq hqi
  have hmain : 2*profileDensity P*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*z=
      2*profileDensity P*t*k*z := by
    calc
      _ = 2*profileDensity P*(((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q))*z := by ring
      _ = _ := by rw [← ratio_factor hpR hqR]; dsimp [t,k]; ring
  change |(p:ℝ)*(profileEnergy (insert q (insert p P))-profileEnergy P)-
    2*profileDensity P*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*z|≤_
  rw [hmain]
  have hexact : (p:ℝ)*(profileEnergy (insert q (insert p P))-profileEnergy P)-
      2*profileDensity P*t*k*z =
      -(p:ℝ)*(profileEnergy P-profileEnergy (insert p P))-
        2*profileDensity (insert q (insert p P))*k*e-
        2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k*z := by
    dsimp [e,k,t,z]
    linear_combination -(p:ℝ)*hrq
  rw [hexact]
  have hfirst : |-(p:ℝ)*(profileEnergy P-profileEnergy (insert p P))|≤
      2*profileDensity P*B/t := by
    rw [hrp,abs_mul,abs_neg,abs_of_pos hpR,abs_mul,abs_mul,
      abs_of_nonneg (by positivity : 0≤2*profileDensity (insert p P)),
      abs_of_nonneg (by positivity : 0≤Real.sqrt p/(p:ℝ)^2)]
    have hm := mul_le_mul_of_nonneg_left hwp
      (show 0≤(p:ℝ)*(2*profileDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2)) by positivity)
    have hdens := mul_le_mul_of_nonneg_right hρple (show 0≤2*B/t by positivity)
    have hs : (p:ℝ)*Real.sqrt p/(p:ℝ)^2=1/t := by rw [mul_div_assoc,sqrt_kernel hpR]; dsimp [t]; field_simp
    calc
      _ ≤ (p:ℝ)*(2*profileDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2))*B := by convert! hm using 1; ring
      _ = profileDensity (insert p P)*(2*B/t) := by
        linear_combination (2*profileDensity (insert p P)*B)*hs
      _ ≤ _ := by convert! hdens using 1; ring
  have hsecond : |2*profileDensity (insert q (insert p P))*k*e|≤2*profileDensity P*D/t := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*profileDensity (insert q (insert p P))*k)]
    have ha := mul_le_mul hρpqle hkle hk hρ.le
    have hb := mul_le_mul ha he (abs_nonneg e) (by positivity)
    convert! mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2) using 1 <;> ring
  have hthird : |2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k*z|≤
      4*profileDensity P*B/t := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k)]
    have hd0 : 0≤profileDensity P-profileDensity (insert q (insert p P)) := sub_nonneg.mpr hρpqle
    have ha := mul_le_mul hρdiff htkin (mul_nonneg ht.le hk) (by positivity)
    have hb := mul_le_mul ha hz (abs_nonneg z) (by positivity)
    have hi := one_div_le_one_div_of_le ht hts
    have hh := mul_le_mul_of_nonneg_left hi (show 0≤4*profileDensity P*B by positivity)
    have hstep : 2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k*|z|≤
        4*profileDensity P*B/(p:ℝ) := by
      convert! mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2) using 1 <;> ring
    exact hstep.trans (by convert! hh using 1 <;> ring)
  calc
    _ ≤ |-(p:ℝ)*(profileEnergy P-profileEnergy (insert p P))-
        2*profileDensity (insert q (insert p P))*k*e|+
        |2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k*z| := abs_sub _ _
    _ ≤ (|-(p:ℝ)*(profileEnergy P-profileEnergy (insert p P))|+
        |2*profileDensity (insert q (insert p P))*k*e|)+
        |2*(profileDensity P-profileDensity (insert q (insert p P)))*t*k*z| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (2*profileDensity P*B/t+2*profileDensity P*D/t)+4*profileDensity P*B/t :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by dsimp [t]; ring

end RHTower
