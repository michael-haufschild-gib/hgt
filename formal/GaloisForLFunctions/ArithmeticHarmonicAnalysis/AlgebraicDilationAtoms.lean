import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequencyRigidity
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilatedVonMangoldtJets
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.PositiveDilationPrimeJetSeparation

/-! Actual prime-power Dirichlet jets embedded into common positive algebraic prime atoms.
The coefficient at a target dilation separates into a nonzero decay factor and
the exact positive-integer incidence row. -/

open Complex
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationAtoms
open AlgebraicPrimeFrequency DilatedVonMangoldt DilationPrimeJets
noncomputable section

/-- Embed the prime-power terms of one dilation into common positive algebraic prime atoms. -/
def primePowerAtom (r : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r)
    (pm : Nat.Primes × ℕ) : PrimeAtom :=
  ⟨pm.1, ⟨(pm.2+1 : ℕ)*r,
    mul_pos (by exact_mod_cast Nat.succ_pos pm.2) hr,
    by simpa only [nsmul_eq_mul] using ha.nsmul (pm.2+1)⟩⟩

theorem primePowerAtom_injective (r : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r) :
    Function.Injective (primePowerAtom r hr ha) := by
  rintro ⟨p,m⟩ ⟨q,n⟩ he
  have hp : p = q := congrArg Prod.fst he
  have hn : ((m+1 : ℕ) : ℝ)*r = ((n+1 : ℕ) : ℝ)*r :=
    congrArg (fun x : PrimeAtom => x.2.val) he
  have hmn : m+1 = n+1 := by exact_mod_cast (mul_right_cancel₀ hr.ne' hn)
  exact Prod.ext hp (Nat.add_right_cancel hmn)

theorem primePowerAtom_frequency (r : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r)
    (pm : Nat.Primes × ℕ) :
    atomFrequency (primePowerAtom r hr ha pm) = r*Real.log ((pm.1.val^(pm.2+1) : ℕ) : ℝ) := by
  simp only [atomFrequency,primePowerAtom,Nat.cast_pow,Real.log_pow]
  ring

/-- The common atom amplitudes are the actual prime-power amplitudes extended by zero. -/
def atomAmplitude (r sigma : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r) (k : ℕ) :
    PrimeAtom → ℂ :=
  Function.extend (primePowerAtom r hr ha) (primeAmplitude r sigma k) (fun _ => 0)

theorem atomAmplitude_primePowerAtom (r sigma : ℝ) (hr : 0 < r)
    (ha : IsAlgebraic ℤ r) (k : ℕ) (pm : Nat.Primes × ℕ) :
    atomAmplitude r sigma hr ha k (primePowerAtom r hr ha pm) =
      primeAmplitude r sigma k pm :=
  (primePowerAtom_injective r hr ha).extend_apply _ _ _

/-- The image condition is exactly positive-integer incidence of the exponent. -/
theorem mem_range_primePowerAtom (r : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r)
    (x : PrimeAtom) :
    x ∈ Set.range (primePowerAtom r hr ha) ↔ ∃ n : ℕ, 0 < n ∧ x.2.val = n*r := by
  constructor
  · rintro ⟨⟨p,m⟩,rfl⟩
    exact ⟨m+1,Nat.succ_pos m,rfl⟩
  · rintro ⟨n,hn,he⟩
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine ⟨(x.1,m),Prod.ext rfl (Subtype.ext ?_)⟩
    exact he.symm

private theorem atomAmplitude_eq_zero_of_not_mem_range
    (r sigma : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r) (k : ℕ)
    (x : PrimeAtom) (hx : x ∉ Set.range (primePowerAtom r hr ha)) :
    atomAmplitude r sigma hr ha k x = 0 :=
  Function.extend_apply' _ _ _ hx

/-- The common atom expansion preserves absolute summability. -/
theorem summable_norm_atomAmplitude (r sigma : ℝ) (hr : 0 < r)
    (ha : IsAlgebraic ℤ r) (k : ℕ) (hs : 1 < r*sigma) :
    Summable fun x => ‖atomAmplitude r sigma hr ha k x‖ := by
  apply (primePowerAtom_injective r hr ha).summable_iff
    (fun x hx => by rw [atomAmplitude_eq_zero_of_not_mem_range r sigma hr ha k x hx,
      norm_zero]) |>.mp
  simpa only [Function.comp_def,atomAmplitude_primePowerAtom] using
    summable_norm_primeAmplitude r sigma k hs

/-- Every actual dilation jet has the same common prime-atom frequency map. -/
theorem source_jet_line_eq_atomSeries (r sigma : ℝ) (hr : 0 < r)
    (ha : IsAlgebraic ℤ r) (k : ℕ) (hs : 1 < r*sigma) (t : ℝ) :
    iteratedDeriv k (source r) ((sigma : ℂ)+(t : ℂ)*I) =
      expSeriesCarrier (atomAmplitude r sigma hr ha k) (fun x => -atomFrequency x) t := by
  rw [source_jet_line_eq_expSeries r sigma k hs t]
  have hsum := (summable_expSeries (summable_norm_primeAmplitude r sigma k hs)
    (fun pm : Nat.Primes × ℕ => -r*Real.log ((pm.1.val^(pm.2+1) : ℕ) : ℝ)) t).hasSum
  have hcommon : HasSum
      (fun x => atomAmplitude r sigma hr ha k x * expChar (-atomFrequency x) t)
      (expSeriesCarrier (primeAmplitude r sigma k)
        (fun pm : Nat.Primes × ℕ => -r*Real.log ((pm.1.val^(pm.2+1) : ℕ) : ℝ)) t) := by
    apply (primePowerAtom_injective r hr ha).hasSum_iff
      (fun x hx => by rw [atomAmplitude_eq_zero_of_not_mem_range r sigma hr ha k x hx,
        zero_mul]) |>.mp
    simpa only [Function.comp_def,atomAmplitude_primePowerAtom,primePowerAtom_frequency,
      expSeriesCarrier,neg_mul] using hsum
  exact hcommon.tsum_eq.symm

/-- At any atom the coefficient is supported exactly on positive-integer exponent incidence. -/
theorem atomAmplitude_eq (r sigma : ℝ) (hr : 0 < r) (ha : IsAlgebraic ℤ r)
    (k : ℕ) (x : PrimeAtom) :
    atomAmplitude r sigma hr ha k x =
      if ∃ n : ℕ, 0 < n ∧ x.2.val = n*r then
        (r : ℂ) * (-(x.2.val : ℂ))^k * (Real.log x.1.val : ℂ)^(k+1) *
          Complex.exp (-(x.2.val*sigma*Real.log x.1.val : ℝ) : ℂ)
      else 0 := by
  by_cases hx : x ∈ Set.range (primePowerAtom r hr ha)
  · obtain ⟨⟨p,m⟩,rfl⟩ := hx
    rw [atomAmplitude_primePowerAtom,primeAmplitude_eq,
      if_pos ((mem_range_primePowerAtom r hr ha _).mp ⟨(p,m),rfl⟩)]
    simp only [primePowerAtom,Complex.ofReal_mul,Complex.ofReal_natCast,neg_mul]
  · rw [atomAmplitude_eq_zero_of_not_mem_range r sigma hr ha k x hx,
      if_neg (fun h => hx ((mem_range_primePowerAtom r hr ha x).mpr h))]

/-- The shared nonzero logarithmic decay factor of a target prime atom. -/
def atomDecay (alpha sigma : ℝ) (p : Nat.Primes) : ℂ :=
  (Real.log p.val : ℂ) * Complex.exp (-(alpha*sigma*Real.log p.val : ℝ) : ℂ)

theorem atomDecay_ne_zero (alpha sigma : ℝ) (p : Nat.Primes) :
    atomDecay alpha sigma p ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  · exact Complex.exp_ne_zero _

/-- Actual atom amplitudes are precisely the normalized prime-jet rows. -/
theorem atomAmplitude_eq_primeJet {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (sigma : ℝ) (j i : ι) (k : ℕ) (p : Nat.Primes) :
    atomAmplitude (r i) sigma (hr i) (ha i) k ⟨p,⟨r j,hr j,ha j⟩⟩ =
      atomDecay (r j) sigma p * primeJet r j p.val i k := by
  rw [atomAmplitude_eq]
  unfold atomDecay primeJet incidence
  by_cases h : ∃ n : ℕ, 0 < n ∧ r j = n*r i
  · simp only [if_pos h,pow_succ]
    ring
  · simp only [if_neg h,zero_mul,mul_zero]

#print axioms primePowerAtom_injective
#print axioms primePowerAtom_frequency
#print axioms atomAmplitude_primePowerAtom
#print axioms mem_range_primePowerAtom
#print axioms summable_norm_atomAmplitude
#print axioms source_jet_line_eq_atomSeries
#print axioms atomAmplitude_eq
#print axioms atomDecay_ne_zero
#print axioms atomAmplitude_eq_primeJet
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationAtoms
