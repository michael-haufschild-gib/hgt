import GaloisForLFunctions.GaloisTheoryOfZeros.AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation
import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw

/-!
# A real collision of mass not divisible by eight gives every signed permutation

Along real times `t > 0` the heat flow `H_t` has finitely many nonreal zeros; their number
`N(t)` (with multiplicity) is the sum of the masses of the later real collisions, where the mass
of a real collision time `s` is `Σ (m − m mod 2)` over its real multiple zeros of order `m`. The
forward monodromy group `G₊` is the group `W` of all signed permutations of finite support or a
subgroup of index two; in the second case the quartets of nonreal zeros are even in number at
every real time off the branch times.

* **Quartets** (`nonrealZeroCount_eq_four_mul`). Off the branch times `N(t) = 4 Q(t)`, `Q(t)` the
  number of zeros in the open first quadrant.
* **Proper group** (`eight_dvd_nonrealZeroCount`, `eight_dvd_collisionMass`). If `G₊ ≠ W`, then
  `8 ∣ N(t)` for every `t > 0` and every real collision has mass divisible by `8`.
* **The criterion** (`mem_forwardMonodromy_of_not_eight_dvd_collisionMass`). A real collision time
  `s > 0` of mass not divisible by `8`, for instance a single double zero at `±x₀`, gives
  `G₊ = W`.

So the sign of `G₊` is read off the real collisions of the de Bruijn–Newman flow: either `G₊ = W`
or every real collision at a positive time moves a multiple of eight zeros. Under RH there is no
real collision at a positive time and this criterion is silent.
-/

noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology RHTower RHTower.DeBruijn
open scoped BigOperators Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- A finite set closed under a fixed-point-free involution `f` that swaps a predicate `P` has
twice as many elements as its `P`-part. -/
theorem ncard_eq_two_mul_of_involution {A : Set ℂ} (f : ℂ → ℂ) (hff : ∀ z, f (f z) = z)
    (hA : A.Finite) (hfA : ∀ z ∈ A, f z ∈ A) (P : ℂ → Prop)
    (hsplit : ∀ z ∈ A, P z ∨ P (f z)) (hdisj : ∀ z ∈ A, P z → ¬ P (f z)) :
    A.ncard = 2 * {z | z ∈ A ∧ P z}.ncard := by
  have hinj : Function.Injective f := Function.LeftInverse.injective hff
  have hU : A = {z | z ∈ A ∧ P z} ∪ f '' {z | z ∈ A ∧ P z} := by
    ext z
    constructor
    · intro hz
      rcases hsplit z hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨f z, ⟨hfA z hz, h⟩, hff z⟩
    · rintro (⟨hz, -⟩ | ⟨w, ⟨hw, -⟩, rfl⟩)
      · exact hz
      · exact hfA w hw
  have hD : Disjoint {z | z ∈ A ∧ P z} (f '' {z | z ∈ A ∧ P z}) := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hz⟩ ⟨w, ⟨hw, hpw⟩, rfl⟩
    exact hdisj w hw hpw hz
  have hfin : {z | z ∈ A ∧ P z}.Finite := hA.subset fun z hz => hz.1
  rw [hU, Set.ncard_union_eq hD hfin (hfin.image f), Set.ncard_image_of_injective _ hinj]
  ring

/-- **Quartets.** Off the branch times the nonreal zeros at a real time are four times the zeros
in the open first quadrant: they are simple, none is imaginary, and `z ↦ −z`, `z ↦ z̄` permute
them. -/
theorem nonrealZeroCount_eq_four_mul {t : ℝ} (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes) :
    nonrealZeroCount t = 4 * (firstQuadrantZeros t).ncard := by
  have hH : complexHeat (t : ℂ) = riemannHeat t := funext (complexHeat_ofReal t)
  set S : Set ℂ := {z | riemannHeat t z = 0 ∧ z.im ≠ 0}
  have hSfin : S.Finite := riemannHeat_nonreal_zeros_finite ht
  -- the nonreal zeros are simple
  have hS : nonrealZeroCount t = S.ncard := by
    rw [nonrealZeroCount_eq ht, Set.ncard_eq_toFinset_card _ hSfin, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz0 := ((Set.Finite.mem_toFinset _).1 hz).1
    refine zeroMult_riemannHeat_eq_one ht.le hz0 fun hd => hb ⟨((t : ℂ), z), ⟨?_, ?_⟩, rfl⟩
    · rw [hH]
      exact hz0
    · rw [hH]
      exact hd
  have hre : ∀ z ∈ S, z.re ≠ 0 := fun z hz =>
    re_ne_zero_of_complexHeat_ofReal_eq_zero (by rw [hH]; exact hz.1)
  -- split by the sign of the real part, then of the imaginary part
  have h1 : S.ncard = 2 * {z | z ∈ S ∧ 0 < z.re}.ncard := by
    refine ncard_eq_two_mul_of_involution (fun z => -z) (fun z => neg_neg z) hSfin
      (fun z hz => ⟨?_, ?_⟩) (fun z => 0 < z.re) (fun z hz => ?_) (fun z _ h h' => ?_)
    · rw [← hH, complexHeat_neg, hH]
      exact hz.1
    · rw [Complex.neg_im, neg_ne_zero]
      exact hz.2
    · rcases lt_or_gt_of_ne (hre z hz) with h | h
      · exact Or.inr (by rw [Complex.neg_re]; linarith only [h])
      · exact Or.inl h
    · rw [Complex.neg_re] at h'
      linarith only [h, h']
  have h2 : {z | z ∈ S ∧ 0 < z.re}.ncard =
      2 * {z | z ∈ {z | z ∈ S ∧ 0 < z.re} ∧ 0 < z.im}.ncard := by
    refine ncard_eq_two_mul_of_involution (starRingEnd ℂ) (fun z => Complex.conj_conj z)
      (hSfin.subset fun z hz => hz.1) (fun z hz => ⟨⟨?_, ?_⟩, ?_⟩) (fun z => 0 < z.im)
      (fun z hz => ?_) (fun z _ h h' => ?_)
    · rw [← hH, complexHeat_ofReal_conj, hH, hz.1.1, map_zero]
    · rw [Complex.conj_im, neg_ne_zero]
      exact hz.1.2
    · rw [Complex.conj_re]
      exact hz.2
    · rcases lt_or_gt_of_ne hz.1.2 with h | h
      · exact Or.inr (by rw [Complex.conj_im]; linarith only [h])
      · exact Or.inl h
    · rw [Complex.conj_im] at h'
      linarith only [h, h']
  have h3 : {z | z ∈ {z | z ∈ S ∧ 0 < z.re} ∧ 0 < z.im} = firstQuadrantZeros t := by
    ext z
    simp only [Set.mem_setOf_eq, firstQuadrantZeros, S, hH]
    constructor
    · rintro ⟨⟨⟨h0, -⟩, hr⟩, hi⟩
      exact ⟨h0, hr, hi⟩
    · rintro ⟨h0, hr, hi⟩
      exact ⟨⟨⟨h0, hi.ne'⟩, hr⟩, hi⟩
  rw [hS, h1, h2, h3]
  ring

/-- Between a time and the next real collision the nonreal count does not change. -/
theorem exists_nonrealZeroCount_eq_right {t : ℝ} (ht : 0 < t) :
    ∃ t' : ℝ, t < t' ∧ (t' : ℂ) ∉ branchTimes ∧ nonrealZeroCount t' = nonrealZeroCount t := by
  -- a radius free of collision times above `t`
  obtain ⟨δ, hδ, hfree⟩ : ∃ δ > 0, ∀ s, t < s → s < t + δ → collisionMass s = 0 := by
    let C := (finite_collisionTimes ht).toFinset
    by_cases hC : C.Nonempty
    · refine ⟨C.inf' hC (fun s => s - t), ?_, fun s hs hst => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro s hs
        have := ((Set.Finite.mem_toFinset _).1 hs).1
        linarith only [this]
      · by_contra hm
        have hsC : s ∈ C := (Set.Finite.mem_toFinset _).2 ⟨hs, hm⟩
        have := Finset.inf'_le (fun s => s - t) hsC
        linarith only [this, hst]
    · refine ⟨1, one_pos, fun s hs _ => ?_⟩
      by_contra hm
      exact hC ⟨s, (Set.Finite.mem_toFinset _).2 ⟨hs, hm⟩⟩
  -- a time in `(t, t + δ)` off the branch times
  have hcount : ((fun s : ℝ => (s : ℂ)) ⁻¹' branchTimes).Countable :=
    countable_branchTimes.preimage Complex.ofReal_injective
  obtain ⟨t', ⟨ht1, ht2⟩, ht'⟩ : ∃ t' ∈ Ioo t (t + δ), (t' : ℂ) ∉ branchTimes := by
    by_contra h
    push_neg at h
    exact (Cardinal.not_countable_real_Ioo (by linarith : t < t + δ)) (hcount.mono h) |>.elim
  refine ⟨t', ht1, ht', ?_⟩
  rw [nonrealZeroCount_eq_collisionMassAfter (ht.trans ht1),
    nonrealZeroCount_eq_collisionMassAfter ht, collisionMassAfter, collisionMassAfter,
    dif_pos (ht.trans ht1), dif_pos ht]
  apply Finset.sum_congr
  · ext s
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hs, hm⟩
      exact ⟨ht1.trans hs, hm⟩
    · rintro ⟨hs, hm⟩
      refine ⟨?_, hm⟩
      by_contra hle
      exact hm (hfree s hs (by linarith [not_lt.1 hle]))
  · exact fun _ _ => rfl

section Proper

variable {b : ℂ} {hb₀ : 0 < b.re} {hbb : b ∉ branchTimes}
  {w : Equiv.Perm {z : ℂ // complexHeat b z = 0}}

/-- **Proper group.** If some signed permutation of finite support is not a forward monodromy,
the number of nonreal zeros is divisible by `8` at every real time `t > 0`. -/
theorem eight_dvd_nonrealZeroCount (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x))
    (hfin : {x | w x ≠ x}.Finite) (hwG : w ∉ forwardMonodromy b hb₀ hbb) {t : ℝ} (ht : 0 < t) :
    8 ∣ nonrealZeroCount t := by
  obtain ⟨t', htt', hb', heq⟩ := exists_nonrealZeroCount_eq_right ht
  rw [← heq, nonrealZeroCount_eq_four_mul (ht.trans htt') hb']
  obtain ⟨k, hk⟩ := even_ncard_firstQuadrantZeros hb₀ hbb hw hfin hwG (ht.trans htt') hb'
  exact ⟨k, by rw [hk]; ring⟩

/-- If `G₊ ≠ W`, every real collision at a positive time has mass divisible by `8`. -/
theorem eight_dvd_collisionMass (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x))
    (hfin : {x | w x ≠ x}.Finite) (hwG : w ∉ forwardMonodromy b hb₀ hbb) {s : ℝ} (hs : 0 < s) :
    8 ∣ collisionMass s := by
  by_cases h8 : 1 / 8 ≤ s
  · rw [collisionMass_eq_zero_of_eighth_le h8]
    exact dvd_zero 8
  obtain ⟨δ, hδ, hleft⟩ := exists_left_nonrealZeroCount hs (le_of_lt (not_le.1 h8))
  set s' := max (s - δ / 2) (s / 2)
  have hs'0 : 0 < s' := lt_max_of_lt_right (by linarith)
  have hs'1 : s - δ < s' := lt_max_of_lt_left (by linarith)
  have hs'2 : s' < s := max_lt (by linarith) (by linarith)
  have heq := hleft s' hs'1 hs'2
  have h1 := eight_dvd_nonrealZeroCount (hb₀ := hb₀) (hbb := hbb) hw hfin hwG hs'0
  have h2 := eight_dvd_nonrealZeroCount (hb₀ := hb₀) (hbb := hbb) hw hfin hwG hs
  rw [heq] at h1
  exact (Nat.dvd_add_right h2).1 h1

end Proper

/-- **The criterion.** A real collision time `s > 0` whose mass is not divisible by `8` gives
`G₊ = W`: every signed permutation of finite support of a forward fibre is a forward monodromy. -/
theorem mem_forwardMonodromy_of_not_eight_dvd_collisionMass {s : ℝ} (hs : 0 < s)
    (hm : ¬ 8 ∣ collisionMass s) {b : ℂ} (hb₀ : 0 < b.re) (hbb : b ∉ branchTimes)
    {w : Equiv.Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hbb := by
  by_contra hwG
  exact hm (eight_dvd_collisionMass hw hfin hwG hs)

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.mem_forwardMonodromy_of_not_eight_dvd_collisionMass
