import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.AffineCollisionMatroid
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import GaloisForLFunctions.HTGeometry.UniversalOrientedHerglotz
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# An explicit digamma Herglotz palette

The residual prime-log construction is not needed to exhibit one explicit Herglotz source.
The shifted digamma function

`g⋆(z) = ψ(z + 1/2) + γ`

has strictly positive imaginary part on the upper half-plane.  The real palette points

`αₙ = 1 / (n + 2)`

are injective and pairwise incongruent modulo the integers.  These are the source-specific
analytic and arithmetic inputs used when the classical joint Gamma-shift theorem supplies
differential independence of the translated palette.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology

noncomputable section

/-- The imaginary part of digamma is strictly positive at every positive height. -/
theorem verticalDigammaIm_pos (sigma t : ℝ) (ht : 0 < t) :
    0 < ReflectedDigammaAnomaly.verticalDigammaIm sigma t := by
  let first : ℝ := t / (sigma ^ (2 : ℕ) + t ^ (2 : ℕ))
  have hfirst : 0 < first := by
    dsimp [first]
    positivity
  have hlim :=
    ReflectedDigammaAnomaly.tendsto_verticalDigammaIm_partialSums (sigma := sigma) ht
  have hbound : ∀ᶠ N : ℕ in atTop,
      first ≤ ∑ n ∈ Finset.range N, t / ((sigma + n) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp [first]
    have hs := Finset.single_le_sum
      (s := Finset.range N)
      (f := fun n : ℕ => t / ((sigma + n) ^ (2 : ℕ) + t ^ (2 : ℕ)))
      (fun n hn => by positivity) (show 0 ∈ Finset.range N by
        simp only [Finset.mem_range]
        omega)
    simpa using hs
  exact lt_of_lt_of_le hfirst (ge_of_tendsto hlim hbound)

/-- The explicit all-positive digamma source.  The real Euler constant does not affect its
imaginary part, and makes the source equal to its Gauss reciprocal-difference series wherever
that series is invoked. -/
def explicitDigammaHerglotzSource (z : ℂ) : ℂ :=
  Complex.digamma (z + (1 / 2 : ℂ)) + (Real.eulerMascheroniConstant : ℂ)

/-- **Explicit Herglotz pointing.**  The canonical shifted digamma source maps the open upper
half-plane strictly into itself. -/
theorem explicitDigammaHerglotzSource_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (explicitDigammaHerglotzSource z).im := by
  have harg :
      (((z.re + 1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) =
        z + (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  have h := verticalDigammaIm_pos (z.re + 1 / 2) z.im hz
  rw [ReflectedDigammaAnomaly.verticalDigammaIm, harg] at h
  simpa [explicitDigammaHerglotzSource] using h

/-- The closed-form real palette point attached to a natural-number code. -/
def explicitDigammaPalettePoint (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem explicitDigammaPalettePoint_pos (n : ℕ) :
    0 < explicitDigammaPalettePoint n := by
  simp [explicitDigammaPalettePoint]
  positivity

theorem explicitDigammaPalettePoint_le_half (n : ℕ) :
    explicitDigammaPalettePoint n ≤ 1 / 2 := by
  rw [explicitDigammaPalettePoint,
    div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)
      (by norm_num : (0 : ℝ) < 2)]
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- The explicit digamma palette has no collisions. -/
theorem explicitDigammaPalettePoint_injective :
    Function.Injective explicitDigammaPalettePoint := by
  intro m n h
  have hm : (m : ℝ) + 2 ≠ 0 := by positivity
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  have hden : (n : ℝ) + 2 = (m : ℝ) + 2 := by
    have hcross := (div_eq_div_iff hm hn).mp h
    simpa [explicitDigammaPalettePoint] using hcross
  exact_mod_cast (by linarith : (m : ℝ) = n)

/-- The collision matroid of the explicit digamma palette is the free matroid: the closed-form
palette contributes one independent frame at every natural-number code. -/
theorem explicitDigammaPalette_collisionMatroid_eq_free :
    affineCollisionMatroid explicitDigammaPalettePoint = Matroid.freeOn Set.univ := by
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [affineCollisionMatroid_indep_iff, Matroid.freeOn_indep_iff]
    exact iff_of_true explicitDigammaPalettePoint_injective.injOn (Set.subset_univ I)

/-- Distinct explicit palette points remain distinct in `ℝ / ℤ`.  This is the periodic-divisor
separation hypothesis in the classical joint Gamma-shift theorem. -/
theorem explicitDigammaPalettePoint_sub_ne_int {m n : ℕ} (hmn : m ≠ n) (k : ℤ) :
    explicitDigammaPalettePoint m - explicitDigammaPalettePoint n ≠ (k : ℝ) := by
  intro h
  have hmpos := explicitDigammaPalettePoint_pos m
  have hnpos := explicitDigammaPalettePoint_pos n
  have hmle := explicitDigammaPalettePoint_le_half m
  have hnle := explicitDigammaPalettePoint_le_half n
  have hklt : k < 1 := by
    have hkltR : (k : ℝ) < 1 := by rw [← h]; linarith
    exact_mod_cast hkltR
  have hkgt : -1 < k := by
    have hkgtR : (-1 : ℝ) < (k : ℝ) := by rw [← h]; linarith
    exact_mod_cast hkgtR
  have hk : k = 0 := by omega
  subst k
  norm_num at h
  exact hmn (explicitDigammaPalettePoint_injective (sub_eq_zero.mp h))

/-! ## Exact finite orientation chambers -/

/-- The explicit digamma source with the residues at a finite set of half-integer poles reversed.
At the pole indexed by `n`, the added rational term changes the residue from `-1` to `+1`. -/
def explicitDigammaFiniteOrientation (J : Finset ℕ) (z : ℂ) : ℂ :=
  explicitDigammaHerglotzSource z +
    ∑ n ∈ J, (2 : ℂ) * (z + (1 / 2 : ℂ) + (n : ℂ))⁻¹

/-- The source with the singular part at the pole indexed by `k` removed. -/
def explicitDigammaFiniteOrientationRegular (J : Finset ℕ) (k : ℕ) (z : ℂ) : ℂ :=
  (Complex.digamma (z + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ)) -
      ∑ j ∈ Finset.range k, (z + (1 / 2 : ℂ) + (j : ℂ))⁻¹ +
      (Real.eulerMascheroniConstant : ℂ)) +
    ∑ n ∈ J.erase k, (2 : ℂ) * (z + (1 / 2 : ℂ) + (n : ℂ))⁻¹

private theorem continuousAt_finset_sum
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℂ → ℂ} {a : ℂ}
    (h : ∀ i ∈ s, ContinuousAt (f i) a) :
    ContinuousAt (fun z => ∑ i ∈ s, f i z) a := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) a)
  | @insert i s hi ih =>
      have hsum := (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using! hsum

/-- The regular background is continuous at the selected half-integer pole. -/
theorem continuousAt_explicitDigammaFiniteOrientationRegular (J : Finset ℕ) (k : ℕ) :
    ContinuousAt (explicitDigammaFiniteOrientationRegular J k)
      (-((k : ℝ) + 1 / 2) : ℂ) := by
  let a : ℂ := (-((k : ℝ) + 1 / 2) : ℂ)
  have harg : a + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ) = 1 := by
    dsimp [a]
    push_cast
    ring
  have hregularDigamma : ContinuousAt
      (fun z : ℂ => Complex.digamma (z + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ))) a := by
    have havoid : ∀ m : ℕ,
        a + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ) ≠ -(m : ℂ) := by
      rw [harg]
      intro m h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hinner : ContinuousAt
        (fun z : ℂ => z + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ)) a := by fun_prop
    have hcomp := ContinuousAt.comp
      (f := fun z : ℂ => z + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ))
      (g := Complex.digamma) (x := a)
      (GaloisForLFunctions.continuousAt_digamma _ havoid) hinner
    simpa only [Function.comp_apply] using! hcomp
  have hregularSum : ContinuousAt
      (fun z : ℂ => ∑ j ∈ Finset.range k,
        (z + (1 / 2 : ℂ) + (j : ℂ))⁻¹) a := by
    apply continuousAt_finset_sum
    intro j hj
    apply ContinuousAt.inv₀ (by fun_prop)
    have hjk : j < k := Finset.mem_range.mp hj
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [a] at hre
    norm_num at hre
    have heq : (j : ℝ) = k := by linarith
    exact (Nat.ne_of_lt hjk) (by exact_mod_cast heq)
  have hbase : ContinuousAt (fun z : ℂ =>
      Complex.digamma (z + (1 / 2 : ℂ) + ((k + 1 : ℕ) : ℂ)) -
        ∑ j ∈ Finset.range k, (z + (1 / 2 : ℂ) + (j : ℂ))⁻¹ +
        (Real.eulerMascheroniConstant : ℂ)) a :=
    (hregularDigamma.sub hregularSum).add continuousAt_const
  have hflips : ContinuousAt (fun z : ℂ =>
      ∑ n ∈ J.erase k, (2 : ℂ) * (z + (1 / 2 : ℂ) + (n : ℂ))⁻¹) a := by
    apply continuousAt_finset_sum
    intro n hn
    apply ContinuousAt.const_mul
    apply ContinuousAt.inv₀ (by fun_prop)
    have hnk : n ≠ k := by simpa using (Finset.mem_erase.mp hn).1
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [a] at hre
    exact hnk (by exact_mod_cast (by linarith : (n : ℝ) = k))
  exact hbase.add hflips

/-- On the upper half-plane, a reversed chamber is the continuous regular background minus one
negative Cauchy atom at any selected reversed pole. -/
theorem explicitDigammaFiniteOrientation_eq_regular_sub_atom
    {J : Finset ℕ} {k : ℕ} (hk : k ∈ J) {z : ℂ} (hz : 0 < z.im) :
    explicitDigammaFiniteOrientation J z =
      explicitDigammaFiniteOrientationRegular J k z -
        (((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹) := by
  let s : ℂ := z + (1 / 2 : ℂ)
  have hs : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    dsimp [s] at him
    simp at him
    linarith
  have hunwind := GaloisForLFunctions.digamma_unwind k s hs
  have hsplit := Finset.sum_erase_add (s := J)
    (f := fun n : ℕ => (2 : ℂ) * (z + (1 / 2 : ℂ) + (n : ℂ))⁻¹) hk
  rw [explicitDigammaFiniteOrientation, explicitDigammaFiniteOrientationRegular, ← hsplit]
  rw [Finset.sum_range_succ] at hunwind
  dsimp [explicitDigammaHerglotzSource, s] at hunwind ⊢
  have hatom : (((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹) =
      -(z + (1 / 2 : ℂ) + (k : ℂ))⁻¹ := by
    rw [show (-((k : ℝ) + 1 / 2) : ℂ) - z =
      -(z + (1 / 2 : ℂ) + (k : ℂ)) by push_cast; ring, inv_neg]
  rw [hunwind]
  have hatomRel :
      (((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹) +
        (z + (1 / 2 : ℂ) + (k : ℂ))⁻¹ = 0 := by
    rw [hatom]
    ring
  linear_combination hatomRel

set_option maxHeartbeats 1000000 in
/-- **Exact explicit digamma chamber law.**  The finite orientation chamber is Herglotz exactly
when no residue is reversed. -/
theorem explicitDigammaFiniteOrientation_nonneg_iff_empty (J : Finset ℕ) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (explicitDigammaFiniteOrientation J z).im) ↔ J = ∅ := by
  constructor
  · intro hnonneg
    by_contra hJ
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
    let a : ℝ := -((k : ℝ) + 1 / 2)
    let g : ℂ → ℂ := explicitDigammaFiniteOrientationRegular J k
    have hpole : (a : ℂ) = (-((k : ℝ) + 1 / 2) : ℂ) := by
      dsimp [a]
      push_cast
      rfl
    have hg : ContinuousAt g (a : ℂ) := by
      rw [hpole]
      exact continuousAt_explicitDigammaFiniteOrientationRegular J k
    obtain ⟨z, hz, hneg⟩ :=
      exists_upper_im_neg_of_continuous_add_negativeAtom a g hg
    have h := hnonneg z hz
    have heq := explicitDigammaFiniteOrientation_eq_regular_sub_atom hk hz
    rw [heq] at h
    have hneg' :
        (explicitDigammaFiniteOrientationRegular J k z -
          (((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹)).im < 0 := by
      simpa only [g, hpole] using hneg
    exact (not_lt_of_ge h) hneg'
  · intro hJ z hz
    subst J
    simpa [explicitDigammaFiniteOrientation] using
      (explicitDigammaHerglotzSource_im_pos hz).le

/-! ## Arbitrary signed completion -/

/-- The Gauss reciprocal-difference series is absolutely summable at every complex parameter.
The usual right-half-plane theorem is extended across the plane by deleting a finite head and
translating the remaining tail into the right half-plane. -/
theorem summable_norm_gaussDigammaSeriesTerm_all (s : ℂ) :
    Summable (fun n : ℕ => ‖RHTower.gaussDigammaSeriesTerm s n‖) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-s.re)
  have hsN : 0 < (s + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hNN : 0 < (((N : ℂ) + 1)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hterm : ∀ n : ℕ,
      RHTower.gaussDigammaSeriesTerm s (n + N) =
        RHTower.gaussDigammaSeriesTerm (s + (N : ℂ)) n -
          RHTower.gaussDigammaSeriesTerm ((N : ℂ) + 1) n := by
    intro n
    simp only [RHTower.gaussDigammaSeriesTerm]
    push_cast
    ring
  have hshift : Summable (fun n : ℕ =>
      ‖RHTower.gaussDigammaSeriesTerm s (n + N)‖) := by
    have h1 := RHTower.summable_norm_gaussDigammaSeriesTerm hsN
    have h2 := RHTower.summable_norm_gaussDigammaSeriesTerm hNN
    apply (h1.add h2).of_nonneg_of_le
    · exact fun n => norm_nonneg _
    intro n
    rw [hterm n]
    exact norm_sub_le _ _
  exact (summable_nat_add_iff N).mp hshift

/-- The signed digamma-completion summand.  The parameter bound `|εₙ| ≤ 1` includes every
orientation sequence with values in `{+1,-1}`. -/
def signedDigammaCompletionTerm (ε : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  (ε n : ℂ) *
    RHTower.gaussDigammaSeriesTerm (z + (1 / 2 : ℂ)) n

/-- Every bounded signed digamma orientation is absolutely summable pointwise. -/
theorem summable_signedDigammaCompletionTerm (ε : ℕ → ℝ) (z : ℂ)
    (hε : ∀ n, |ε n| ≤ 1) :
    Summable (signedDigammaCompletionTerm ε z) := by
  apply Summable.of_norm_bounded
    (summable_norm_gaussDigammaSeriesTerm_all (z + (1 / 2 : ℂ)))
  intro n
  rw [signedDigammaCompletionTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnonneg :
      0 ≤ ‖RHTower.gaussDigammaSeriesTerm (z + (1 / 2 : ℂ)) n‖ := norm_nonneg _
  nlinarith [hε n]

/-- The canonical pointwise sum attached to an arbitrary bounded orientation sequence. -/
def signedDigammaCompletion (ε : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, signedDigammaCompletionTerm ε z n

/-- Canonical finite chambers converge to the signed digamma completion at every point. -/
theorem tendsto_signedDigammaCompletion_partialSums (ε : ℕ → ℝ) (z : ℂ)
    (hε : ∀ n, |ε n| ≤ 1) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, signedDigammaCompletionTerm ε z n)
      atTop (nhds (signedDigammaCompletion ε z)) := by
  have hs := summable_signedDigammaCompletionTerm ε z hε
  exact (hs.hasSum_iff_tendsto_nat).mp hs.hasSum

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology

noncomputable section

/-- The finite Gauss sum identity holds at every parameter off the digamma pole lattice. -/
theorem sum_gaussDigammaSeriesTerm_eq_digamma_shift_of_offPoles
    (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (N : ℕ) :
    (∑ n ∈ Finset.range N, RHTower.gaussDigammaSeriesTerm s n) =
      Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) -
        (Complex.digamma (s + N) - Complex.digamma ((N : ℂ) + 1)) := by
  rw [RHTower.digamma_apply_add_nat s hs N, RHTower.digamma_natCast_add_one N]
  simp_rw [RHTower.gaussDigammaSeriesTerm]
  rw [Finset.sum_sub_distrib]
  have hone :
      (∑ n ∈ Finset.range N, (1 : ℂ) / ((n : ℂ) + 1)) =
        ((harmonic N : ℝ) : ℂ) := by
    symm
    exact RHTower.harmonic_cast_eq N
  rw [hone]
  ring

/-- Gauss's reciprocal-difference series represents digamma everywhere off its pole lattice, not
only on the initial right half-plane. -/
theorem tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles
    (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    (∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s n) =
      Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-s.re)
  have hsN : 0 < (s + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hNN : 0 < (((N : ℂ) + 1)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hsum : Summable (RHTower.gaussDigammaSeriesTerm s) :=
    (summable_norm_gaussDigammaSeriesTerm_all s).of_norm
  have hshift : Summable (RHTower.gaussDigammaSeriesTerm (s + (N : ℂ))) :=
    RHTower.summable_gaussDigammaSeriesTerm hsN
  have hnat : Summable (RHTower.gaussDigammaSeriesTerm ((N : ℂ) + 1)) :=
    RHTower.summable_gaussDigammaSeriesTerm hNN
  have hterm : ∀ n : ℕ,
      RHTower.gaussDigammaSeriesTerm s (n + N) =
        RHTower.gaussDigammaSeriesTerm (s + (N : ℂ)) n -
          RHTower.gaussDigammaSeriesTerm ((N : ℂ) + 1) n := by
    intro n
    simp only [RHTower.gaussDigammaSeriesTerm]
    push_cast
    ring
  have hshiftEq :
      (∑' n : ℕ, RHTower.gaussDigammaSeriesTerm (s + (N : ℂ)) n) =
        Complex.digamma (s + N) + (Real.eulerMascheroniConstant : ℂ) := by
    have h := RHTower.digamma_eq_neg_euler_add_tsum_gauss hsN
    linear_combination -h
  have hnatEq :
      (∑' n : ℕ, RHTower.gaussDigammaSeriesTerm ((N : ℂ) + 1) n) =
        Complex.digamma ((N : ℂ) + 1) +
          (Real.eulerMascheroniConstant : ℂ) := by
    have h := RHTower.digamma_eq_neg_euler_add_tsum_gauss hNN
    linear_combination -h
  calc
    (∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s n) =
        (∑ n ∈ Finset.range N, RHTower.gaussDigammaSeriesTerm s n) +
          ∑' n : ℕ, RHTower.gaussDigammaSeriesTerm s (n + N) :=
      (hsum.sum_add_tsum_nat_add N).symm
    _ = (∑ n ∈ Finset.range N, RHTower.gaussDigammaSeriesTerm s n) +
        ((∑' n : ℕ, RHTower.gaussDigammaSeriesTerm (s + (N : ℂ)) n) -
          ∑' n : ℕ, RHTower.gaussDigammaSeriesTerm ((N : ℂ) + 1) n) := by
      congr 1
      rw [tsum_congr hterm, hshift.tsum_sub hnat]
    _ = Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) := by
      rw [sum_gaussDigammaSeriesTerm_eq_digamma_shift_of_offPoles s hs N,
        hshiftEq, hnatEq]
      ring

/-- The all-positive signed Gauss completion is exactly the explicit shifted-digamma source. -/
theorem signedDigammaCompletion_one_eq_explicitDigammaHerglotzSource
    {z : ℂ} (hz : ∀ n : ℕ, z + (1 / 2 : ℂ) ≠ -(n : ℂ)) :
    signedDigammaCompletion (fun _ => 1) z = explicitDigammaHerglotzSource z := by
  rw [signedDigammaCompletion, explicitDigammaHerglotzSource]
  simp only [signedDigammaCompletionTerm, Complex.ofReal_one, one_mul]
  exact tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles
    (z + (1 / 2 : ℂ)) hz

end

end GaloisForLFunctions.HTGeometry
