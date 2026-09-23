import Mathlib
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.StablePrimitiveExactness

/-!
# The arithmetic mixed prime/depth rate and its stable quotient

For a real function `f` of a prime and a depth, the *mixed boundary* at base prime `b` is the
rectangular difference

`B^b_{P,M} f = f(P,M) − f(P,0) − f(b,M) + f(b,0)`,

and the *mixed rate* is the joint limit

`q f = lim_{P→∞, M→∞} B^(2 : ℕ)_{P,M} f / ((log P − log 2) M)`.

The radial space consists of the functions whose mixed boundary is `O_p(M)` at every fixed prime
and whose mixed rate exists.  Its rectangular differential `D` produces a two-term complex whose
cocycles are exactly its coboundaries, so ordinary cohomology vanishes, while the stable quotient
by the kernel of the rate is canonically the real line.

This file proves:

* the mixed rate is a well-defined linear functional on the radial space;
* it is independent of the chosen base prime;
* `f_a(p,m) = a m log p` realizes every rate, so the rate is surjective;
* a function killed by the rectangular differential has zero rate;
* consequently the stable-primitive group `D R / D S` is canonically `ℝ`, while ordinary
  cohomology of the radial complex vanishes.
-/

namespace RHTower

open Filter Topology GaloisForLFunctions.HTGeometry.Interfinity

noncomputable section

/-! ## The prime/depth source complex -/

/-- Real functions of a prime and a depth. -/
abbrev PrimeDepthFunction := Nat.Primes → ℕ → ℝ

/-- Rectangular cochains in the prime and the depth direction. -/
abbrev PrimeDepthRectCochain := Nat.Primes → Nat.Primes → ℕ → ℕ → ℝ

/-- The fixed base prime. -/
def basePrime : Nat.Primes := ⟨2, Nat.prime_two⟩

@[simp] theorem basePrime_cast : ((basePrime.1 : ℕ) : ℝ) = 2 := by
  norm_num [basePrime]

/-- The full rectangular difference `(Df)(p,q;m,n)`. -/
def rectDiff (f : PrimeDepthFunction) (p q : Nat.Primes) (m n : ℕ) : ℝ :=
  f p m - f p n - f q m + f q n

/-- The mixed boundary `B^b_{P,M} f` at base prime `b`. -/
def mixedBoundary (b : Nat.Primes) (f : PrimeDepthFunction) (P : Nat.Primes) (M : ℕ) : ℝ :=
  rectDiff f P b M 0

theorem mixedBoundary_add (b : Nat.Primes) (f g : PrimeDepthFunction) (P : Nat.Primes) (M : ℕ) :
    mixedBoundary b (f + g) P M = mixedBoundary b f P M + mixedBoundary b g P M := by
  simp only [mixedBoundary, rectDiff, Pi.add_apply]
  ring

theorem mixedBoundary_smul (b : Nat.Primes) (c : ℝ) (f : PrimeDepthFunction) (P : Nat.Primes)
    (M : ℕ) : mixedBoundary b (c • f) P M = c * mixedBoundary b f P M := by
  simp only [mixedBoundary, rectDiff, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem mixedBoundary_zero (b : Nat.Primes) (P : Nat.Primes) (M : ℕ) :
    mixedBoundary b (0 : PrimeDepthFunction) P M = 0 := by
  simp [mixedBoundary, rectDiff]

/-- The mixed boundary at base `b` is the difference of two mixed boundaries at base `2`. -/
theorem mixedBoundary_base_sub (b : Nat.Primes) (f : PrimeDepthFunction) (P : Nat.Primes)
    (M : ℕ) :
    mixedBoundary b f P M = mixedBoundary basePrime f P M - mixedBoundary basePrime f b M := by
  simp only [mixedBoundary, rectDiff]
  ring

/-! ## The joint prime/depth limit filter -/

/-- Primes tending to infinity. -/
def primeAtTop : Filter Nat.Primes := Filter.comap (fun p : Nat.Primes => (p.1 : ℕ)) atTop

theorem tendsto_primeAtTop : Tendsto (fun p : Nat.Primes => (p.1 : ℕ)) primeAtTop atTop :=
  Filter.tendsto_comap

instance primeAtTop_neBot : primeAtTop.NeBot := by
  rw [primeAtTop, Filter.comap_neBot_iff]
  intro t ht
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 ht
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  exact ⟨(⟨p, hp⟩ : Nat.Primes), hN p hpN⟩

theorem eventually_large_prime (n : ℕ) : ∀ᶠ p : Nat.Primes in primeAtTop, n ≤ p.1 :=
  tendsto_primeAtTop.eventually (Filter.eventually_ge_atTop n)

theorem tendsto_log_primeAtTop :
    Tendsto (fun p : Nat.Primes => Real.log (p.1 : ℝ)) primeAtTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_primeAtTop)

/-- The joint prime/depth limit filter. -/
def mixedFilter : Filter (Nat.Primes × ℕ) := primeAtTop ×ˢ atTop

instance mixedFilter_neBot : mixedFilter.NeBot :=
  Filter.prod_neBot.2 ⟨inferInstance, inferInstance⟩

theorem tendsto_log_mixedFilter :
    Tendsto (fun x : Nat.Primes × ℕ => Real.log (x.1.1 : ℝ)) mixedFilter atTop :=
  tendsto_log_primeAtTop.comp Filter.tendsto_fst

theorem eventually_mixedFilter (n m : ℕ) :
    ∀ᶠ x : Nat.Primes × ℕ in mixedFilter, n ≤ x.1.1 ∧ m ≤ x.2 :=
  (eventually_large_prime n).prod_mk (Filter.eventually_ge_atTop m)

/-- A ratio of two shifts of a variable tending to infinity tends to one. -/
theorem tendsto_sub_div_sub_atTop (c d : ℝ) :
    Tendsto (fun x : ℝ => (x - c) / (x - d)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => x - d) atTop atTop :=
    tendsto_atTop_add_const_right _ (-d) tendsto_id
  have h2 : Tendsto (fun x : ℝ => (d - c) / (x - d)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds h1
  have h3 : Tendsto (fun x : ℝ => 1 + (d - c) / (x - d)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h2
  refine h3.congr' ?_
  filter_upwards [h1.eventually_gt_atTop 0] with x hx
  field_simp
  ring

/-! ## The mixed rate -/

/-- The mixed-rate quotient at base prime `b`. -/
def mixedRatio (b : Nat.Primes) (f : PrimeDepthFunction) (x : Nat.Primes × ℕ) : ℝ :=
  mixedBoundary b f x.1 x.2 / ((Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ)) * x.2)

theorem mixedRatio_add (b : Nat.Primes) (f g : PrimeDepthFunction) :
    mixedRatio b (f + g) = mixedRatio b f + mixedRatio b g := by
  funext x
  simp only [mixedRatio, mixedBoundary_add, Pi.add_apply, add_div]

theorem mixedRatio_smul (b : Nat.Primes) (c : ℝ) (f : PrimeDepthFunction) :
    mixedRatio b (c • f) = c • mixedRatio b f := by
  funext x
  simp only [mixedRatio, mixedBoundary_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

@[simp] theorem mixedRatio_zero (b : Nat.Primes) :
    mixedRatio b (0 : PrimeDepthFunction) = 0 := by
  funext x
  simp [mixedRatio]

/-- Condition `(2)`: at every fixed prime the mixed boundary grows at most linearly in the
depth. -/
def LocallyLinearBoundary (f : PrimeDepthFunction) : Prop :=
  ∀ p : Nat.Primes, ∃ C : ℝ, ∀ M : ℕ, |mixedBoundary basePrime f p M| ≤ C * M

/-- The mixed rate of `f` is `L`. -/
def HasMixedRate (f : PrimeDepthFunction) (L : ℝ) : Prop :=
  Tendsto (mixedRatio basePrime f) mixedFilter (𝓝 L)

/-- The radial space: locally linear mixed boundary, and an existing mixed rate. -/
def radialSpace : Submodule ℝ PrimeDepthFunction where
  carrier := {f | LocallyLinearBoundary f ∧ ∃ L : ℝ, HasMixedRate f L}
  add_mem' := by
    rintro f g ⟨hfb, Lf, hf⟩ ⟨hgb, Lg, hg⟩
    refine ⟨fun p => ?_, Lf + Lg, ?_⟩
    · obtain ⟨Cf, hCf⟩ := hfb p
      obtain ⟨Cg, hCg⟩ := hgb p
      refine ⟨Cf + Cg, fun M => ?_⟩
      rw [mixedBoundary_add]
      calc |mixedBoundary basePrime f p M + mixedBoundary basePrime g p M|
          ≤ |mixedBoundary basePrime f p M| + |mixedBoundary basePrime g p M| := abs_add_le _ _
        _ ≤ Cf * M + Cg * M := add_le_add (hCf M) (hCg M)
        _ = (Cf + Cg) * M := by ring
    · show Tendsto (mixedRatio basePrime (f + g)) mixedFilter (𝓝 (Lf + Lg))
      rw [mixedRatio_add]
      exact hf.add hg
  zero_mem' := by
    refine ⟨fun p => ⟨0, fun M => by simp⟩, 0, ?_⟩
    show Tendsto (mixedRatio basePrime (0 : PrimeDepthFunction)) mixedFilter (𝓝 0)
    rw [mixedRatio_zero]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c f ⟨hfb, L, hf⟩
    refine ⟨fun p => ?_, c * L, ?_⟩
    · obtain ⟨C, hC⟩ := hfb p
      refine ⟨|c| * C, fun M => ?_⟩
      rw [mixedBoundary_smul, abs_mul]
      calc |c| * |mixedBoundary basePrime f p M| ≤ |c| * (C * M) :=
            mul_le_mul_of_nonneg_left (hC M) (abs_nonneg c)
        _ = |c| * C * M := by ring
    · show Tendsto (mixedRatio basePrime (c • f)) mixedFilter (𝓝 (c * L))
      rw [mixedRatio_smul]
      exact hf.const_smul c

theorem mem_radialSpace_iff {f : PrimeDepthFunction} :
    f ∈ radialSpace ↔ LocallyLinearBoundary f ∧ ∃ L : ℝ, HasMixedRate f L := Iff.rfl

/-- The mixed rate as a linear functional on the radial space. -/
def mixedRate : radialSpace →ₗ[ℝ] ℝ where
  toFun f := Filter.limUnder mixedFilter (mixedRatio basePrime f.1)
  map_add' f g := by
    obtain ⟨Lf, hf⟩ := f.2.2
    obtain ⟨Lg, hg⟩ := g.2.2
    have hfg : Tendsto (mixedRatio basePrime ((f : PrimeDepthFunction) + g)) mixedFilter
        (𝓝 (Lf + Lg)) := by
      rw [mixedRatio_add]
      exact hf.add hg
    rw [hf.limUnder_eq, hg.limUnder_eq]
    exact hfg.limUnder_eq
  map_smul' c f := by
    obtain ⟨L, hf⟩ := f.2.2
    have hcf : Tendsto (mixedRatio basePrime (c • (f : PrimeDepthFunction))) mixedFilter
        (𝓝 (c * L)) := by
      rw [mixedRatio_smul]
      exact hf.const_smul c
    rw [hf.limUnder_eq]
    exact hcf.limUnder_eq

/-- The mixed rate is the actual limit. -/
theorem hasMixedRate_mixedRate (f : radialSpace) :
    HasMixedRate (f : PrimeDepthFunction) (mixedRate f) := by
  obtain ⟨L, hL⟩ := f.2.2
  show Tendsto (mixedRatio basePrime (f : PrimeDepthFunction)) mixedFilter
    (𝓝 (Filter.limUnder mixedFilter (mixedRatio basePrime (f : PrimeDepthFunction))))
  rwa [hL.limUnder_eq]

theorem mixedRate_eq {f : radialSpace} {L : ℝ} (hL : HasMixedRate (f : PrimeDepthFunction) L) :
    mixedRate f = L := hL.limUnder_eq

/-! ## Base-prime independence -/

/-- **Base independence.**  Replacing the base prime by any other fixed prime does not change the
mixed rate of a radial function. -/
theorem tendsto_mixedRatio_of_base (b : Nat.Primes) {f : PrimeDepthFunction}
    (hf : LocallyLinearBoundary f) {L : ℝ} (hL : HasMixedRate f L) :
    Tendsto (mixedRatio b f) mixedFilter (𝓝 L) := by
  obtain ⟨C, hC⟩ := hf b
  have hC0 : 0 ≤ C := by
    have h1 := hC 1
    have h2 : (0 : ℝ) ≤ |mixedBoundary basePrime f b 1| := abs_nonneg _
    simp only [Nat.cast_one, mul_one] at h1
    linarith
  have hev : ∀ᶠ x : Nat.Primes × ℕ in mixedFilter, max 3 (b.1 + 1) ≤ x.1.1 ∧ 1 ≤ x.2 :=
    eventually_mixedFilter _ _
  have hkey : ∀ x : Nat.Primes × ℕ, max 3 (b.1 + 1) ≤ x.1.1 → 1 ≤ x.2 →
      Real.log 2 < Real.log (x.1.1 : ℝ) ∧ Real.log (b.1 : ℝ) < Real.log (x.1.1 : ℝ) ∧
        (0 : ℝ) < x.2 := by
    intro x hP hM
    have hP3 : (3 : ℕ) ≤ x.1.1 := le_trans (le_max_left _ _) hP
    have hPb : b.1 + 1 ≤ x.1.1 := le_trans (le_max_right _ _) hP
    have h2R : (2 : ℝ) < (x.1.1 : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hP3
    have hbR : ((b.1 : ℕ) : ℝ) < (x.1.1 : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega) hPb
    have hbpos : (0 : ℝ) < (b.1 : ℝ) := by exact_mod_cast b.2.pos
    refine ⟨Real.log_lt_log (by norm_num) h2R, Real.log_lt_log hbpos hbR, ?_⟩
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM
  have hratio : Tendsto (fun x : Nat.Primes × ℕ =>
      (Real.log (x.1.1 : ℝ) - Real.log 2) / (Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ)))
      mixedFilter (𝓝 1) :=
    (tendsto_sub_div_sub_atTop (Real.log 2) (Real.log (b.1 : ℝ))).comp tendsto_log_mixedFilter
  have hdiv : Tendsto (fun x : Nat.Primes × ℕ =>
      Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ)) mixedFilter atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right mixedFilter (-Real.log (b.1 : ℝ)) tendsto_log_mixedFilter
  have htail : Tendsto (fun x : Nat.Primes × ℕ =>
      mixedBoundary basePrime f b x.2 /
        ((Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ)) * x.2)) mixedFilter (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop (f := fun _ => C) tendsto_const_nhds hdiv)
    filter_upwards [hev] with x hx
    obtain ⟨-, hv, hM⟩ := hkey x hx.1 hx.2
    have hv0 : 0 < Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ) := by linarith
    have hden : 0 < (Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ)) * x.2 := mul_pos hv0 hM
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hv0]
    have hb := hC x.2
    nlinarith [abs_nonneg (mixedBoundary basePrime f b x.2)]
  have hmain := (hL.mul hratio).sub htail
  rw [mul_one, sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [hev] with x hx
  obtain ⟨hu, hv, hM⟩ := hkey x hx.1 hx.2
  have hu0 : Real.log (x.1.1 : ℝ) - Real.log 2 ≠ 0 := by linarith
  have hv0 : Real.log (x.1.1 : ℝ) - Real.log (b.1 : ℝ) ≠ 0 := by linarith
  have hM0 : ((x.2 : ℝ)) ≠ 0 := ne_of_gt hM
  simp only [mixedRatio, mixedBoundary_base_sub b f x.1 x.2, basePrime_cast]
  field_simp

/-- The base-`b` mixed rate of a radial function equals its base-`2` mixed rate. -/
theorem limUnder_mixedRatio_base (b : Nat.Primes) (f : radialSpace) :
    Filter.limUnder mixedFilter (mixedRatio b (f : PrimeDepthFunction)) = mixedRate f :=
  (tendsto_mixedRatio_of_base b f.2.1 (hasMixedRate_mixedRate f)).limUnder_eq

/-! ## Realizing every rate -/

/-- The linear depth model `f_a(p,m) = a m log p`. -/
def linearWitness (a : ℝ) : PrimeDepthFunction := fun p m => a * m * Real.log (p.1 : ℝ)

theorem mixedBoundary_linearWitness (b : Nat.Primes) (a : ℝ) (P : Nat.Primes) (M : ℕ) :
    mixedBoundary b (linearWitness a) P M =
      a * M * (Real.log (P.1 : ℝ) - Real.log (b.1 : ℝ)) := by
  simp only [mixedBoundary, rectDiff, linearWitness, Nat.cast_zero]
  ring

theorem locallyLinearBoundary_linearWitness (a : ℝ) :
    LocallyLinearBoundary (linearWitness a) := by
  intro p
  refine ⟨|a * (Real.log (p.1 : ℝ) - Real.log (basePrime.1 : ℝ))|, fun M => ?_⟩
  rw [mixedBoundary_linearWitness,
    show a * M * (Real.log (p.1 : ℝ) - Real.log (basePrime.1 : ℝ)) =
      (a * (Real.log (p.1 : ℝ) - Real.log (basePrime.1 : ℝ))) * M by ring,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

theorem hasMixedRate_linearWitness (a : ℝ) : HasMixedRate (linearWitness a) a := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_mixedFilter 3 1] with x hx
  have h2R : (2 : ℝ) < (x.1.1 : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hx.1
  have hu : Real.log 2 < Real.log (x.1.1 : ℝ) := Real.log_lt_log (by norm_num) h2R
  have hM : (0 : ℝ) < x.2 := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hx.2
  have hne : (Real.log (x.1.1 : ℝ) - Real.log 2) ≠ 0 := by linarith
  have hM0 : ((x.2 : ℝ)) ≠ 0 := ne_of_gt hM
  simp only [mixedRatio, mixedBoundary_linearWitness, basePrime_cast]
  field_simp

theorem linearWitness_mem (a : ℝ) : linearWitness a ∈ radialSpace :=
  ⟨locallyLinearBoundary_linearWitness a, a, hasMixedRate_linearWitness a⟩

@[simp] theorem mixedRate_linearWitness (a : ℝ) :
    mixedRate ⟨linearWitness a, linearWitness_mem a⟩ = a :=
  mixedRate_eq (hasMixedRate_linearWitness a)

theorem mixedRate_surjective : Function.Surjective mixedRate := fun a =>
  ⟨⟨linearWitness a, linearWitness_mem a⟩, mixedRate_linearWitness a⟩

/-! ## The radial two-term complex -/

/-- The rectangular differential. -/
def rectD : PrimeDepthFunction →ₗ[ℝ] PrimeDepthRectCochain where
  toFun f := fun p q m n => rectDiff f p q m n
  map_add' f g := by
    funext p q m n
    simp only [rectDiff, Pi.add_apply]
    ring
  map_smul' c f := by
    funext p q m n
    simp only [rectDiff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem rectD_apply (f : PrimeDepthFunction) (p q : Nat.Primes) (m n : ℕ) :
    rectD f p q m n = rectDiff f p q m n := rfl

/-- The rectangular differential restricted to the radial space. -/
def radialD : radialSpace →ₗ[ℝ] PrimeDepthRectCochain := rectD.comp radialSpace.subtype

@[simp] theorem radialD_apply (f : radialSpace) (p q : Nat.Primes) (m n : ℕ) :
    radialD f p q m n = rectDiff (f : PrimeDepthFunction) p q m n := rfl

/-- The radial slice: the cocycles of the top degree are exactly its coboundaries. -/
def radialSlice : CochainSlice ℝ radialSpace PrimeDepthRectCochain where
  d := radialD
  cocycles := LinearMap.range radialD
  range_le := le_rfl

@[simp] theorem radialSlice_d : radialSlice.d = radialD := rfl

@[simp] theorem radialSlice_cocycles : radialSlice.cocycles = LinearMap.range radialD := rfl

theorem radialSlice_exact : radialSlice.cocycles ≤ LinearMap.range radialSlice.d := le_rfl

/-- **Ordinary cohomology of the radial complex vanishes.** -/
theorem subsingleton_radialSlice_ordinaryH : Subsingleton radialSlice.OrdinaryH := by
  constructor
  intro x y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.eq, radialSlice.stableBoundary_top_eq_top radialSlice_exact]
  trivial

/-- The critical mixed bornology `S = ker q`. -/
def stableSpace : Submodule ℝ radialSpace := LinearMap.ker mixedRate

/-- A function killed by the rectangular differential has zero mixed rate. -/
theorem mixedRate_eq_zero_of_radialD_eq_zero {f : radialSpace} (h : radialD f = 0) :
    mixedRate f = 0 := by
  have hzero : mixedRatio basePrime (f : PrimeDepthFunction) = 0 := by
    funext x
    have : rectDiff (f : PrimeDepthFunction) x.1 basePrime x.2 0 = 0 := by
      have := congrFun (congrFun (congrFun (congrFun h x.1) basePrime) x.2) 0
      simpa using this
    simp [mixedRatio, mixedBoundary, this]
  refine mixedRate_eq ?_
  show Tendsto (mixedRatio basePrime (f : PrimeDepthFunction)) mixedFilter (𝓝 0)
  rw [hzero]
  exact tendsto_const_nhds

theorem ker_radialD_le_stableSpace : LinearMap.ker radialD ≤ stableSpace := by
  intro f hf
  exact mixedRate_eq_zero_of_radialD_eq_zero hf

theorem stableSpace_sup_ker : stableSpace ⊔ LinearMap.ker radialSlice.d = stableSpace :=
  sup_eq_left.2 ker_radialD_le_stableSpace

/-! ## The one-dimensional stable quotient -/

/-- **The mixed rate identifies the degree-two stable-primitive group with the real line.** -/
def mixedRateQuotientEquiv : radialSlice.StableH stableSpace ≃ₗ[ℝ] ℝ :=
  (radialSlice.dbarEquiv radialSlice_exact stableSpace).symm.trans
    ((Submodule.quotEquivOfEq _ _ stableSpace_sup_ker).trans
      (mixedRate.quotKerEquivOfSurjective mixedRate_surjective))

@[simp] theorem mixedRateQuotientEquiv_apply (f : radialSpace) :
    mixedRateQuotientEquiv (Submodule.Quotient.mk (radialSlice.dRes f)) = mixedRate f := by
  have hsymm : (radialSlice.dbarEquiv radialSlice_exact stableSpace).symm
      (Submodule.Quotient.mk (radialSlice.dRes f)) = Submodule.Quotient.mk f :=
    (radialSlice.dbarEquiv radialSlice_exact stableSpace).symm_apply_eq.2 rfl
  simp only [mixedRateQuotientEquiv, LinearEquiv.trans_apply, hsymm]
  rfl

end

end RHTower
