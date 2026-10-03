import GaloisForLFunctions.RHTower.ChiPrimeGaussianProgressionProfile

/-!
# The full moving Gaussian prime profile near every fixed rational frequency

Finite residue partition retains all primes, the actual rational phase and the
complete physical window. The source progression theorem supplies its quantitative
error. Constants are uniform over the rational numerator and physical ratio.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Full prime profile with both its exact rational phase and residual frequency. -/
def primeGaussianRationalProfile (A Q : ℕ) (ξ N τ : ℝ) : ℂ :=
  ∑ p∈primeProfileBand N,
    (primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N)))*
      primeRationalPhase A Q p

/-- The signed reduced-residue mean of the actual rational phase. -/
def primeGaussianRationalProfileMean (A Q : ℕ) [NeZero Q] : ℂ := by
  classical
  exact (∑ a∈(Finset.univ : Finset (ZMod Q)).filter IsUnit,
    primeRationalPhase A Q a.val)/(Q.totient:ℂ)

private theorem rational_profile_partition (A Q : ℕ) [NeZero Q] (f : ℕ→ℂ)
    {N : ℝ} (hN : (Q:ℝ)≤N) :
    (∑ p∈primeProfileBand N, f p*primeRationalPhase A Q p) =
      ∑ a∈(Finset.univ : Finset (ZMod Q)).filter IsUnit,
        primeRationalPhase A Q a.val*(∑ p∈primeProgressionBand Q a N,f p) := by
  classical
  let R := (Finset.univ : Finset (ZMod Q)).filter IsUnit
  have hQ : 0<Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hN0 : 0≤N := (Nat.cast_nonneg Q).trans hN
  have hmap : ∀ p∈primeProfileBand N, (p:ZMod Q)∈R := by
    intro p hp
    obtain ⟨hpI,hprime⟩ := Finset.mem_filter.mp hp
    have hpN : N<(p:ℝ) := (Nat.floor_lt hN0).mp (Finset.mem_Ioc.mp hpI).1
    have hQp : Q<p := by exact_mod_cast hN.trans_lt hpN
    have hcop : p.Coprime Q := hprime.coprime_iff_not_dvd.mpr (fun hd =>
      (not_le_of_gt hQp) (Nat.le_of_dvd hQ hd))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ZMod.isUnit_iff_coprime p Q).mpr hcop⟩
  have hphase (p:ℕ) : primeRationalPhase A Q p = primeRationalPhase A Q (p:ZMod Q).val := by
    simpa only [ZMod.val_natCast] using primeRationalPhase_mod A hQ p
  have hfilter (a:ZMod Q) : (primeProfileBand N).filter (fun p:ℕ => (p:ZMod Q)=a) =
      primeProgressionBand Q a N := by
    ext p
    simp only [primeProfileBand,primeProgressionBand,Finset.mem_filter,and_assoc]
  have hrewrite : (∑ p∈primeProfileBand N, f p*primeRationalPhase A Q p) =
      ∑ p∈primeProfileBand N, f p*primeRationalPhase A Q (p:ZMod Q).val := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hphase p]
  rw [hrewrite,← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hfilter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2.2]
  ring

/-- The full rational profile has its signed residue mean, uniformly in every
numerator, physical ratio and residual frequency. No prime or profile estimate is
assumed; all primes in the original band are retained. -/
theorem exists_primeGaussianRationalProfile_power_log (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ A:ℕ, ∀ ξ∈Icc (1/2:ℝ) 2, ∀ τ:ℝ,
      ‖(Real.log N:ℂ)*primeGaussianRationalProfile A Q ξ N τ/(N:ℂ)-
        primeGaussianRationalProfileMean A Q*(∫ x in (1:ℝ)..2,
          primeGaussianScaledLogProfile ξ (1/Real.log N) x*bourgainOscillation (τ*x))‖ ≤
        C*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by
  classical
  obtain ⟨c,B,X,hc,hB,hX,hbound⟩ := exists_primeGaussianProgressionProfile_power_log Q
  let R := (Finset.univ : Finset (ZMod Q)).filter IsUnit
  refine ⟨c,B*((R.card:ℝ)+1),max X (Q:ℝ),hc,by positivity,hX.trans (le_max_left _ _),?_⟩
  intro N hN A ξ hξ τ
  have hNX : X≤N := (le_max_left _ _).trans hN
  have hNQ : (Q:ℝ)≤N := (le_max_right _ _).trans hN
  let f : ℕ→ℂ := fun p => primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N))
  let S : ZMod Q→ℂ := fun a => ∑ p∈primeProgressionBand Q a N,f p
  let J : ℂ := ∫ x in (1:ℝ)..2,
    primeGaussianScaledLogProfile ξ (1/Real.log N) x*bourgainOscillation (τ*x)
  let ell : ℂ := (Q.totient:ℂ)⁻¹
  let D : ZMod Q→ℂ := fun a => (Real.log N:ℂ)*S a/(N:ℂ)-ell*J
  have hsplit : primeGaussianRationalProfile A Q ξ N τ =
      ∑ a∈R,primeRationalPhase A Q a.val*S a := rational_profile_partition A Q f hNQ
  have hmain : (∑ a∈R,primeRationalPhase A Q a.val*(ell*J)) =
      primeGaussianRationalProfileMean A Q*J := by
    rw [← Finset.sum_mul]
    dsimp only [primeGaussianRationalProfileMean,ell,R]
    ring
  have hident : (Real.log N:ℂ)*primeGaussianRationalProfile A Q ξ N τ/(N:ℂ)-
      primeGaussianRationalProfileMean A Q*J = ∑ a∈R,primeRationalPhase A Q a.val*D a := by
    symm
    simp only [D,mul_sub,Finset.sum_sub_distrib,hmain]
    congr 1
    rw [hsplit,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hterm (a:ZMod Q) (ha:a∈R) : ‖primeRationalPhase A Q a.val*D a‖≤
      B*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by
    rw [norm_mul,primeRationalPhase,norm_bourgainOscillation,one_mul]
    exact hbound N hNX a (Finset.mem_filter.mp ha).2 ξ hξ τ
  change ‖(Real.log N:ℂ)*primeGaussianRationalProfile A Q ξ N τ/(N:ℂ)-
    primeGaussianRationalProfileMean A Q*J‖≤_
  rw [hident]
  calc
    _ ≤ ∑ a∈R,‖primeRationalPhase A Q a.val*D a‖ := norm_sum_le _ _
    _ ≤ ∑ a∈R,B*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := Finset.sum_le_sum hterm
    _ = (R.card:ℝ)*B*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _ ≤ _ := by
      have hp : 0≤B*(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10))) := by positivity
      nlinarith only [hp]

/-- The whole prime row near a fixed rational denominator has quantitative
inverse-frequency control, retaining its actual moving physical window. -/
theorem exists_primeGaussianRationalProfile_fourier_bound (Q : ℕ) [NeZero Q] :
    ∃ c C N₀ : ℝ, 0<c ∧ 0<C ∧ 3≤N₀ ∧ ∀ N:ℝ, N₀≤N →
      ∀ A:ℕ, ∀ ξ∈Icc (1/2:ℝ) 2, ∀ τ:ℝ, τ≠0 →
      ‖primeGaussianRationalProfile A Q ξ N τ‖ ≤
        C*N/Real.log N*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))) := by
  classical
  obtain ⟨c,B,X,hc,hB,hX,hbound⟩ := exists_primeGaussianProgressionProfile_fourier_bound Q
  let R := (Finset.univ : Finset (ZMod Q)).filter IsUnit
  refine ⟨c,B*((R.card:ℝ)+1),max X (Q:ℝ),hc,by positivity,hX.trans (le_max_left _ _),?_⟩
  intro N hN A ξ hξ τ hτ
  have hNX : X≤N := (le_max_left _ _).trans hN
  have hNQ : (Q:ℝ)≤N := (le_max_right _ _).trans hN
  have hN0 : 0<N := by linarith only [hX,hNX]
  have hL : 0<Real.log N := Real.log_pos (by linarith only [hX,hNX])
  let f : ℕ→ℂ := fun p => primeGaussianScaledProfile ξ ((p:ℝ)/N)*bourgainOscillation (τ*((p:ℝ)/N))
  rw [primeGaussianRationalProfile,rational_profile_partition A Q f hNQ]
  apply (norm_sum_le _ _).trans
  have hterm (a:ZMod Q) (ha:a∈R) :
      ‖primeRationalPhase A Q a.val*(∑ p∈primeProgressionBand Q a N,f p)‖≤
        B*N/Real.log N*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))) := by
    rw [norm_mul,primeRationalPhase,norm_bourgainOscillation,one_mul]
    exact hbound N hNX a (Finset.mem_filter.mp ha).2 ξ hξ τ hτ
  apply (Finset.sum_le_sum hterm).trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hp : 0≤B*N/Real.log N*(1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))) := by positivity
  have heq : B*((R.card:ℝ)+1)*N/Real.log N =
      ((R.card:ℝ)+1)*(B*N/Real.log N) := by ring
  rw [heq]
  nlinarith only [hp]

end RHTower
