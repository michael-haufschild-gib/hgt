import GaloisForLFunctions.HTGeometry.StretchedExponentialFiniteDifference
import GaloisForLFunctions.HTGeometry.SuperIncreasingValuationGap
import Mathlib.Data.Finsupp.Multiset

open Filter Finset Set Asymptotics Topology

/-!
# Convex confinement for stretched-exponential valuations

For `0 < α < 1`, the consecutive increments of `exp (n ^ α)` eventually set strict new records.
Moving one unit from a sufficiently large coordinate to a smaller coordinate therefore strictly
decreases both the stretched-exponential valuation and the quadratic spread of an integer tuple.

The well-founded smoothing theorem `exists_boundaryShell_of_sum_bounds` reduces every tuple outside
a fixed window to a tuple on the next finite boundary shell.  Fixed boundary shells are then
separated from a least-shift fixed-offset witness by the first- or second-moment finite-difference
asymptotics.  The capstone `exists_eventually_bounded_stretchedMinimizer` proves the unconditional
bounded-minimizer lemma: every minimizer in any varying finite collection with fixed arity, a fixed
source-sum window, and a least-shift witness has all coordinates `q + O(1)`.
-/

namespace GaloisForLFunctions

noncomputable section

def stretchedIncrement (α : ℝ) (n : ℕ) : ℝ :=
  stretchedExp α (n + 1) - stretchedExp α n

private def firstDifference : ℕ →₀ ℝ :=
  Finsupp.single 1 1 - Finsupp.single 0 1

private lemma firstDifference_moment_zero : stretchedMoment firstDifference 0 = 0 := by
  rw [stretchedMoment, firstDifference, Finsupp.sum_sub_index]
  · simp
  · intro a b₁ b₂
    ring

private lemma firstDifference_moment_one : stretchedMoment firstDifference 1 = 1 := by
  rw [stretchedMoment, firstDifference, Finsupp.sum_sub_index]
  · simp
  · intro a b₁ b₂
    ring

private lemma stretchedFiniteDifference_firstDifference (α x : ℝ) :
    stretchedFiniteDifference α firstDifference x =
      stretchedExp α (x + 1) - stretchedExp α x := by
  rw [stretchedFiniteDifference, firstDifference, Finsupp.sum_sub_index]
  · simp
  · intro a b₁ b₂
    ring

lemma tendsto_stretchedIncrement_atTop {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (stretchedIncrement α) atTop atTop := by
  have hlead : Tendsto (stretchedFiniteDifferenceLeading α firstDifference 1) atTop atTop := by
    have hcore := (tendsto_exp_div_rpow_atTop ((1 - α) / α)).comp
      (tendsto_rpow_atTop hα0)
    have hcore' : Tendsto
        (fun x : ℝ => Real.exp (x ^ α) / (x ^ α) ^ ((1 - α) / α))
        atTop atTop := by simpa using hcore
    have heq : (fun x : ℝ => stretchedFiniteDifferenceLeading α firstDifference 1 x) =ᶠ[atTop]
        fun x => α * (Real.exp (x ^ α) / (x ^ α) ^ ((1 - α) / α)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [stretchedFiniteDifferenceLeading]
      rw [firstDifference_moment_one]
      simp only [Nat.factorial_one, Nat.cast_one, div_one,
        pow_one]
      rw [← Real.rpow_mul hx.le]
      have hexp : α * ((1 - α) / α) = 1 - α := by field_simp
      rw [hexp]
      rw [div_eq_mul_inv]
      rw [show (1 : ℝ) * α - 1 = -(1 - α) by ring]
      rw [Real.rpow_neg (le_of_lt hx)]
      ring
    exact (hcore'.const_mul_atTop hα0).congr' heq.symm
  have hequiv := stretchedFiniteDifference_isEquivalent hα0 hα1 firstDifference 1
    (by intro k hk; interval_cases k; exact firstDifference_moment_zero)
    (firstDifference_moment_one ▸ one_ne_zero)
  have hreal : Tendsto (fun x : ℝ => stretchedFiniteDifference α firstDifference x) atTop atTop :=
    hequiv.symm.tendsto_atTop hlead
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  simpa [stretchedIncrement, stretchedFiniteDifference_firstDifference] using hnat

lemma eventually_pos_iteratedDeriv_two_stretchedExp {α : ℝ} (hα0 : 0 < α) :
    ∀ᶠ x : ℝ in atTop, 0 < (deriv^[2] (stretchedExp α)) x := by
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < stretchedDerivativeLeading α 2 x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [stretchedDerivativeLeading]
    positivity
  simpa only [iteratedDeriv_eq_iterate] using
    (iteratedDeriv_stretchedExp_isEquivalent hα0 2).eventually_pos hpos

lemma exists_strictConvexOn_stretchedExp_Ici {α : ℝ} (hα0 : 0 < α) :
    ∃ T : ℝ, StrictConvexOn ℝ (Ici T) (stretchedExp α) := by
  obtain ⟨T₀, hT₀⟩ := (eventually_atTop.1 (eventually_pos_iteratedDeriv_two_stretchedExp hα0))
  let T := max T₀ 1
  have hT : ∀ x, T ≤ x → 0 < (deriv^[2] (stretchedExp α)) x := by
    intro x hx
    exact hT₀ x ((le_max_left T₀ 1).trans hx)
  refine ⟨T, strictConvexOn_of_deriv2_pos' (D := Ici T)
    (convex_Ici T : Convex ℝ (Ici T)) ?_ ?_⟩
  · intro x hx
    have hx1 : 1 ≤ x := (le_max_right T₀ 1).trans hx
    exact (Real.continuous_exp.continuousAt.comp
      (Real.continuousAt_rpow_const x α (Or.inl (by linarith)))).continuousWithinAt
  · intro x hx
    exact hT x hx

lemma exists_stretchedIncrement_record_strict {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Q : ℕ, ∀ a b : ℕ, Q ≤ b → a < b →
      stretchedIncrement α a < stretchedIncrement α b := by
  obtain ⟨T, hconv⟩ := exists_strictConvexOn_stretchedExp_Ici hα0
  obtain ⟨Tn, hTn⟩ := exists_nat_ge T
  have hadj : ∀ n ≥ Tn,
      stretchedIncrement α n < stretchedIncrement α (n + 1) := by
    intro n hn
    have hnT : T ≤ (n : ℝ) := hTn.trans (by exact_mod_cast hn)
    have hslope := hconv.slope_strict_mono_adjacent
      (x := (n : ℝ)) (y := (n : ℝ) + 1) (z := (n : ℝ) + 2)
      hnT (by simp only [Set.mem_Ici]; linarith) (by linarith) (by linarith)
    norm_num at hslope
    dsimp [stretchedIncrement]
    push_cast
    ring_nf at hslope ⊢
    exact hslope
  have htail : StrictMono (fun r : ℕ => stretchedIncrement α (Tn + r)) := by
    apply strictMono_nat_of_lt_succ
    intro r
    simpa [Nat.add_assoc] using hadj (Tn + r) (Nat.le_add_right Tn r)
  have hprefix : ∀ᶠ b : ℕ in atTop, ∀ a ∈ Finset.range Tn,
      stretchedIncrement α a < stretchedIncrement α b := by
    rw [Filter.eventually_all_finset]
    intro a ha
    exact (tendsto_stretchedIncrement_atTop hα0 hα1).eventually
      (eventually_gt_atTop (stretchedIncrement α a))
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 hprefix
  let Q := max Q₀ Tn
  refine ⟨Q, fun a b hQb hab => ?_⟩
  by_cases ha : a < Tn
  · exact hQ₀ b ((le_max_left Q₀ Tn).trans hQb) a (Finset.mem_range.mpr ha)
  · have hTa : Tn ≤ a := Nat.le_of_not_gt ha
    have hTb : Tn ≤ b := hTa.trans hab.le
    have hsub : a - Tn < b - Tn := Nat.sub_lt_sub_right hTa hab
    simpa [Nat.add_sub_of_le hTa, Nat.add_sub_of_le hTb] using htail hsub

def smoothTuple {D : ℕ} (s : Fin D → ℕ) (lo hi : Fin D) : Fin D → ℕ :=
  Function.update (Function.update s hi (s hi - 1)) lo (s lo + 1)

lemma smoothTuple_apply_lo {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D} :
    smoothTuple s lo hi lo = s lo + 1 := by
  simp [smoothTuple]

lemma smoothTuple_apply_hi {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi) :
    smoothTuple s lo hi hi = s hi - 1 := by
  simp [smoothTuple, Ne.symm hne]

lemma smoothTuple_apply_of_ne {D : ℕ} (s : Fin D → ℕ) {lo hi k : Fin D}
    (hklo : k ≠ lo) (hkhi : k ≠ hi) :
    smoothTuple s lo hi k = s k := by
  simp [smoothTuple, hklo, hkhi]

lemma comp_smoothTuple_eq_updates {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D}
    (hne : lo ≠ hi) {A : Type*} (g : ℕ → A) :
    (fun i => g (smoothTuple s lo hi i)) =
      Function.update
        (Function.update (fun i => g (s i)) hi (g (s hi - 1)))
        lo (g (s lo + 1)) := by
  funext k
  by_cases hklo : k = lo
  · subst k
    simp [smoothTuple]
  by_cases hkhi : k = hi
  · subst k
    simp [smoothTuple, Ne.symm hne]
  · simp [smoothTuple, hklo, hkhi]

lemma sum_eq_two_add_rest {D : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin D → A) {lo hi : Fin D} (hne : lo ≠ hi) :
    ∑ i, f i = f lo + f hi + ∑ i ∈ (Finset.univ.erase lo).erase hi, f i := by
  classical
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ lo)]
  simp only [Finset.sdiff_singleton_eq_erase]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
    (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ hi⟩)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ac_rfl

lemma sum_comp_smoothTuple {D : ℕ} {A : Type*} [AddCommMonoid A]
    (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi) (g : ℕ → A) :
    ∑ i, g (smoothTuple s lo hi i) =
      g (s lo + 1) + g (s hi - 1) +
        ∑ i ∈ (Finset.univ.erase lo).erase hi, g (s i) := by
  rw [sum_eq_two_add_rest (fun i => g (smoothTuple s lo hi i)) hne,
    smoothTuple_apply_lo s, smoothTuple_apply_hi s hne]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i hiMem
  rw [smoothTuple_apply_of_ne]
  · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hiMem).2).1
  · exact (Finset.mem_erase.mp hiMem).1

lemma sum_smoothTuple {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D}
    (hne : lo ≠ hi) (hhi : 0 < s hi) :
    ∑ i, smoothTuple s lo hi i = ∑ i, s i := by
  classical
  have hsmooth := sum_comp_smoothTuple s hne (fun n => n)
  simp only at hsmooth
  rw [hsmooth, sum_eq_two_add_rest s hne]
  omega

def tupleEnergy {D : ℕ} (s : Fin D → ℕ) : ℕ :=
  ∑ i, (s i) ^ 2

lemma tupleEnergy_smoothTuple_lt {D : ℕ} (s : Fin D → ℕ) {lo hi : Fin D}
    (hne : lo ≠ hi) (hgap : s lo + 1 < s hi) :
    tupleEnergy (smoothTuple s lo hi) < tupleEnergy s := by
  classical
  rw [tupleEnergy, tupleEnergy]
  rw [sum_comp_smoothTuple s hne (fun n => n ^ 2),
    sum_eq_two_add_rest (fun i => (s i) ^ 2) hne]
  have hhi : 0 < s hi := by omega
  have hsplit : s hi = (s hi - 1) + 1 := by omega
  rw [hsplit]
  simp only [Nat.add_sub_cancel, pow_two]
  nlinarith

def tupleStretchedValuation (α : ℝ) {D : ℕ} (s : Fin D → ℕ) : ℝ :=
  ∑ i, stretchedExp α (s i)

/-- **Convex smoothing lowers the valuation, for any increment-record weight.**  Moving one unit
from a high coordinate to a low one strictly decreases `∑ g (s i)` as soon as the increments of `g`
are strictly increasing from `Q` on.  Both the polynomial-power and the stretched-exponential
weights are instances. -/
lemma sum_comp_smoothTuple_lt {D Q : ℕ} (g : ℕ → ℝ)
    (hrecord : ∀ a b : ℕ, Q ≤ b → a < b → g (a + 1) - g a < g (b + 1) - g b)
    (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi)
    (hQ : Q ≤ s hi - 1) (hgap : s lo + 1 < s hi) :
    ∑ i, g (smoothTuple s lo hi i) < ∑ i, g (s i) := by
  classical
  rw [sum_comp_smoothTuple s hne g, sum_eq_two_add_rest (fun i => g (s i)) hne]
  have hhi : 0 < s hi := by omega
  have hinc := hrecord (s lo) (s hi - 1) hQ (by omega)
  have hsub : (s hi - 1 : ℕ) + 1 = s hi := Nat.sub_add_cancel hhi
  rw [hsub] at hinc
  linarith

lemma tupleStretchedValuation_smoothTuple_lt {α : ℝ} {D Q : ℕ}
    (hrecord : ∀ a b : ℕ, Q ≤ b → a < b →
      stretchedIncrement α a < stretchedIncrement α b)
    (s : Fin D → ℕ) {lo hi : Fin D} (hne : lo ≠ hi)
    (hQ : Q ≤ s hi - 1) (hgap : s lo + 1 < s hi) :
    tupleStretchedValuation α (smoothTuple s lo hi) < tupleStretchedValuation α s :=
  sum_comp_smoothTuple_lt (fun n => stretchedExp α n)
    (fun a b hQb hab => by
      have h := hrecord a b hQb hab
      dsimp [stretchedIncrement] at h
      push_cast
      linarith [h])
    s hne hQ hgap

def tupleInWindow (q K : ℕ) {D : ℕ} (s : Fin D → ℕ) : Prop :=
  ∀ i, q ≤ s i + K ∧ s i ≤ q + K

theorem exists_boundaryShell_of_sum_bounds_of_smoothing
    {D q K C : ℕ} (hD : 0 < D) (hKC : C < K)
    (V : (Fin D → ℕ) → ℝ)
    (hsmooth : ∀ (s : Fin D → ℕ) (lo hi : Fin D), lo ≠ hi →
      q ≤ s hi → s lo + 1 < s hi → V (smoothTuple s lo hi) ≤ V s)
    (s : Fin D → ℕ)
    (hsumLower : D * q ≤ ∑ i, s i)
    (hsumUpper : ∑ i, s i ≤ D * q + C)
    (hout : ¬ tupleInWindow q K s) :
    ∃ t : Fin D → ℕ,
      ∑ i, t i = ∑ i, s i ∧
      tupleInWindow q (K + 1) t ∧
      ¬ tupleInWindow q K t ∧
      V t ≤ V s := by
  classical
  induction hE : tupleEnergy s using Nat.strong_induction_on generalizing s with
  | h E ih =>
      by_cases hshell : tupleInWindow q (K + 1) s
      · exact ⟨s, rfl, hshell, hout, le_rfl⟩
      · have hbad : ∃ i, s i + (K + 1) < q ∨ q + (K + 1) < s i := by
          rw [tupleInWindow] at hshell
          obtain ⟨i, hi⟩ := not_forall.mp hshell
          refine ⟨i, ?_⟩
          by_cases hlo : q ≤ s i + (K + 1)
          · right
            have hhi : ¬ s i ≤ q + (K + 1) := fun h => hi ⟨hlo, h⟩
            omega
          · left
            omega
        obtain ⟨i, hiLow | hiHigh⟩ := hbad
        · have huniv : (Finset.univ : Finset (Fin D)).Nonempty := by
            obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hD
            exact ⟨i₀, Finset.mem_univ i₀⟩
          have hconst : (∑ _j : Fin D, q) ≤ ∑ j, s j := by
            simpa using hsumLower
          obtain ⟨j, _hjmem, hj⟩ := Finset.exists_le_of_sum_le huniv hconst
          have hne : i ≠ j := by
            intro hij
            subst j
            omega
          let s' := smoothTuple s i j
          have hjpos : 0 < s j := by omega
          have hsum : ∑ k, s' k = ∑ k, s k :=
            sum_smoothTuple s hne hjpos
          have hgap : s i + 1 < s j := by omega
          have henergy : tupleEnergy s' < E := by
            rw [← hE]
            exact tupleEnergy_smoothTuple_lt s hne hgap
          have hout' : ¬ tupleInWindow q K s' := by
            intro hin
            have hlo := (hin i).1
            change q ≤ smoothTuple s i j i + K at hlo
            rw [smoothTuple_apply_lo s] at hlo
            omega
          obtain ⟨t, htsum, htwide, htout, htval⟩ :=
            ih (tupleEnergy s') henergy s'
              (by rw [hsum]; exact hsumLower)
              (by rw [hsum]; exact hsumUpper) hout' rfl
          exact ⟨t, htsum.trans hsum, htwide, htout,
            htval.trans (hsmooth s i j hne hj hgap)⟩
        · have huniv : (Finset.univ : Finset (Fin D)).Nonempty := by
            obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hD
            exact ⟨i₀, Finset.mem_univ i₀⟩
          have hsumConst : (∑ j, s j) ≤ ∑ _j : Fin D, (q + C) := by
            calc
              ∑ j, s j ≤ D * q + C := hsumUpper
              _ ≤ D * (q + C) := by nlinarith
              _ = ∑ _j : Fin D, (q + C) := by simp [Nat.mul_add]
          obtain ⟨j, _hjmem, hj⟩ := Finset.exists_le_of_sum_le huniv hsumConst
          have hne : j ≠ i := by
            intro hij
            subst j
            omega
          let s' := smoothTuple s j i
          have hipos : 0 < s i := by omega
          have hsum : ∑ k, s' k = ∑ k, s k :=
            sum_smoothTuple s hne hipos
          have hgap : s j + 1 < s i := by omega
          have henergy : tupleEnergy s' < E := by
            rw [← hE]
            exact tupleEnergy_smoothTuple_lt s hne hgap
          have hout' : ¬ tupleInWindow q K s' := by
            intro hin
            have hhi := (hin i).2
            change smoothTuple s j i i ≤ q + K at hhi
            rw [smoothTuple_apply_hi s hne] at hhi
            omega
          obtain ⟨t, htsum, htwide, htout, htval⟩ :=
            ih (tupleEnergy s') henergy s'
              (by rw [hsum]; exact hsumLower)
              (by rw [hsum]; exact hsumUpper) hout' rfl
          exact ⟨t, htsum.trans hsum, htwide, htout,
            htval.trans (hsmooth s j i hne (by omega) hgap)⟩

/-- **Boundary-shell smoothing for any increment-record weight.**  A tuple whose coordinate sum is
pinned to `[D q, D q + C]` but which leaves the window `q ± K` can be smoothed, without changing the
sum, to one that sits exactly on the shell `q ± (K+1)` and has no larger weight `∑ g`.  The only
property of `g` used is that its increments strictly increase from `Q` on. -/
lemma exists_boundaryShell_of_sum_bounds_of_record {D q K C Q : ℕ} (g : ℕ → ℝ)
    (hD : 0 < D) (hKC : C < K) (hqQ : Q + 1 ≤ q)
    (hrecord : ∀ a b : ℕ, Q ≤ b → a < b → g (a + 1) - g a < g (b + 1) - g b)
    (s : Fin D → ℕ)
    (hsumLower : D * q ≤ ∑ i, s i)
    (hsumUpper : ∑ i, s i ≤ D * q + C)
    (hout : ¬ tupleInWindow q K s) :
    ∃ t : Fin D → ℕ,
      ∑ i, t i = ∑ i, s i ∧
      tupleInWindow q (K + 1) t ∧
      ¬ tupleInWindow q K t ∧
      ∑ i, g (t i) ≤ ∑ i, g (s i) :=
  exists_boundaryShell_of_sum_bounds_of_smoothing hD hKC (fun u => ∑ i, g (u i))
    (fun s lo hi hne hq hgap =>
      (sum_comp_smoothTuple_lt g hrecord s hne (by omega) hgap).le)
    s hsumLower hsumUpper hout

lemma exists_boundaryShell_of_sum_bounds {α : ℝ} {D q K C Q : ℕ}
    (hD : 0 < D) (hKC : C < K) (hqQ : Q + 1 ≤ q)
    (hrecord : ∀ a b : ℕ, Q ≤ b → a < b →
      stretchedIncrement α a < stretchedIncrement α b)
    (s : Fin D → ℕ)
    (hsumLower : D * q ≤ ∑ i, s i)
    (hsumUpper : ∑ i, s i ≤ D * q + C)
    (hout : ¬ tupleInWindow q K s) :
    ∃ t : Fin D → ℕ,
      ∑ i, t i = ∑ i, s i ∧
      tupleInWindow q (K + 1) t ∧
      ¬ tupleInWindow q K t ∧
      tupleStretchedValuation α t ≤ tupleStretchedValuation α s := by
  obtain ⟨t, hsum, hshell, hout', hval⟩ :=
    exists_boundaryShell_of_sum_bounds_of_record (fun n => stretchedExp α n) hD hKC hqQ
      (fun a b hQb hab => by
        have h := hrecord a b hQb hab
        dsimp [stretchedIncrement] at h
        push_cast
        linarith [h])
      s hsumLower hsumUpper hout
  exact ⟨t, hsum, hshell, hout', hval⟩

def tupleDifference {D : ℕ} (u v : Fin D → ℕ) : ℕ →₀ ℝ :=
  (∑ i, Finsupp.single (u i) 1) - ∑ i, Finsupp.single (v i) 1

lemma stretchedMoment_tupleDifference {D : ℕ} (u v : Fin D → ℕ) (k : ℕ) :
    stretchedMoment (tupleDifference u v) k =
      (∑ i, (u i : ℝ) ^ k) - ∑ i, (v i : ℝ) ^ k := by
  classical
  rw [stretchedMoment, tupleDifference, Finsupp.sum_sub_index]
  · have hsum (w : Fin D → ℕ) :
        (∑ i, Finsupp.single (w i) (1 : ℝ)).sum
            (fun r a => a * (r : ℝ) ^ k) = ∑ i, (w i : ℝ) ^ k := by
      rw [← Finsupp.sum_finsetSum_index (s := Finset.univ)
        (g := fun i => Finsupp.single (w i) (1 : ℝ))
        (h := fun r a => a * (r : ℝ) ^ k)]
      · simp
      · intro a
        simp
      · intro a b₁ b₂
        ring
    rw [hsum u, hsum v]
  · intro a b₁ b₂
    ring

lemma stretchedFiniteDifference_tupleDifference {α x : ℝ} {D : ℕ}
    (u v : Fin D → ℕ) :
    stretchedFiniteDifference α (tupleDifference u v) x =
      (∑ i, stretchedExp α (x + u i)) - ∑ i, stretchedExp α (x + v i) := by
  classical
  rw [stretchedFiniteDifference, tupleDifference, Finsupp.sum_sub_index]
  · have hsum (w : Fin D → ℕ) :
        (∑ i, Finsupp.single (w i) (1 : ℝ)).sum
            (fun r a => a * stretchedExp α (x + r)) =
          ∑ i, stretchedExp α (x + w i) := by
      rw [← Finsupp.sum_finsetSum_index (s := Finset.univ)
        (g := fun i => Finsupp.single (w i) (1 : ℝ))
        (h := fun r a => a * stretchedExp α (x + r))]
      · simp
      · intro a
        simp
      · intro a b₁ b₂
        ring
    rw [hsum u, hsum v]
  · intro a b₁ b₂
    ring

lemma eventually_log_lt_stretchedFiniteDifference {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : 0 < stretchedMoment d j) :
    ∀ᶠ x : ℝ in atTop, Real.log x < stretchedFiniteDifference α d x := by
  have hleadPos : ∀ᶠ x : ℝ in atTop,
      0 < stretchedFiniteDifferenceLeading α d j x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [stretchedFiniteDifferenceLeading]
    exact mul_pos (mul_pos (div_pos (mul_pos hmoment (pow_pos hα0 _)) (by positivity))
      (Real.exp_pos _)) (Real.rpow_pos_of_pos hx _)
  have hequiv := stretchedFiniteDifference_isEquivalent hα0 hα1 d j hcancel hmoment.ne'
  have hdiffPos := hequiv.eventually_pos hleadPos
  have hlogAbs := (log_isLittleO_abs_stretchedFiniteDifference hα0 hα1 d j
    hcancel hmoment.ne').eventuallyLT_norm_of_eventually_pos
      (hdiffPos.mono fun x hx => by simpa [Real.norm_eq_abs, abs_of_pos hx] using hx)
  filter_upwards [hdiffPos, hlogAbs] with x hx hlt
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_of_pos hx] at hlt
  exact (le_abs_self _).trans_lt hlt

lemma sum_sq_sub_sum_sq_eq_centered {D : ℕ} (u v : Fin D → ℝ) (L : ℝ)
    (hsum : ∑ i, u i = ∑ i, v i) :
    (∑ i, (u i) ^ 2) - ∑ i, (v i) ^ 2 =
      (∑ i, (u i - L) ^ 2) - ∑ i, (v i - L) ^ 2 := by
  have hu : (∑ i, (u i) ^ 2) =
      ∑ i, ((u i - L) ^ 2 + (2 * L) * u i - L ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hv : (∑ i, (v i) ^ 2) =
      ∑ i, ((v i - L) ^ 2 + (2 * L) * v i - L ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hu, hv]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]
  ring

def boundaryOffsetCandidate {D L : ℕ} (δ : Fin D → ℕ)
    (u : Fin D → Fin (2 * L + 1)) : Prop :=
  (∑ i, (δ i + L)) ≤ ∑ i, (u i : ℕ) ∧
    ∃ i, (u i : ℕ) = 0 ∨ (u i : ℕ) = 2 * L

lemma boundaryOffsetCandidate_moment_one_nonneg {D L : ℕ} (δ : Fin D → ℕ)
    (u : Fin D → Fin (2 * L + 1)) (hu : boundaryOffsetCandidate δ u) :
    0 ≤ stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 := by
  rw [stretchedMoment_tupleDifference]
  simp only [pow_one]
  rw [sub_nonneg]
  norm_cast
  simpa only using hu.1

lemma boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero {D L : ℕ}
    (δ : Fin D → ℕ) (u : Fin D → Fin (2 * L + 1))
    (hu : boundaryOffsetCandidate δ u)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (hmoment1 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 1 = 0) :
    0 < stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 2 := by
  have hsum : (∑ i, ((u i : ℕ) : ℝ)) = ∑ i, ((δ i + L : ℕ) : ℝ) := by
    rw [stretchedMoment_tupleDifference] at hmoment1
    simpa only [pow_one, sub_eq_zero] using hmoment1
  have hcenter := sum_sq_sub_sum_sq_eq_centered
    (fun i => ((u i : ℕ) : ℝ)) (fun i => ((δ i + L : ℕ) : ℝ)) L hsum
  have hvcenter : (∑ i, ((((δ i + L : ℕ) : ℝ)) - (L : ℝ)) ^ 2) =
      ∑ i, (δ i : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hvcenter] at hcenter
  obtain ⟨i, hi0 | hi2⟩ := hu.2
  · have hterm : ((((u i : ℕ) : ℝ) - (L : ℝ)) ^ 2) = (L : ℝ) ^ 2 := by
      rw [hi0]
      push_cast
      ring
    have hbound : (L : ℝ) ^ 2 ≤
        ∑ j, ((((u j : ℕ) : ℝ) - (L : ℝ)) ^ 2) := by
      rw [← hterm]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin D => ((((u j : ℕ) : ℝ) - (L : ℝ)) ^ 2))
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [stretchedMoment_tupleDifference]
    rw [hcenter]
    linarith
  · have hterm : ((((u i : ℕ) : ℝ) - (L : ℝ)) ^ 2) = (L : ℝ) ^ 2 := by
      rw [hi2]
      push_cast
      ring
    have hbound : (L : ℝ) ^ 2 ≤
        ∑ j, ((((u j : ℕ) : ℝ) - (L : ℝ)) ^ 2) := by
      rw [← hterm]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin D => ((((u j : ℕ) : ℝ) - (L : ℝ)) ^ 2))
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [stretchedMoment_tupleDifference]
    rw [hcenter]
    linarith

lemma boundaryOffsetCandidate_eventually_log_gap {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (u : Fin D → Fin (2 * L + 1)) (hu : boundaryOffsetCandidate δ u) :
    ∀ᶠ x : ℝ in atTop, Real.log x <
      stretchedFiniteDifference α
        (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  have hm0 : stretchedMoment
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) 0 = 0 := by
    rw [stretchedMoment_tupleDifference]
    simp
  have hm1nn := boundaryOffsetCandidate_moment_one_nonneg δ u hu
  rcases hm1nn.eq_or_lt with hm1 | hm1
  · have hm2 := boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero δ u hu hLsq hm1.symm
    exact eventually_log_lt_stretchedFiniteDifference hα0 hα1 _ 2
      (by
        intro k hk
        interval_cases k
        · exact hm0
        · exact hm1.symm) hm2
  · exact eventually_log_lt_stretchedFiniteDifference hα0 hα1 _ 1
      (by intro k hk; interval_cases k; exact hm0) hm1

lemma boundaryOffsetCandidate_eventually_all_log_gap {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2) :
    ∀ᶠ x : ℝ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u → Real.log x <
        stretchedFiniteDifference α
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  rw [Filter.eventually_all]
  intro u
  by_cases hu : boundaryOffsetCandidate δ u
  · exact (boundaryOffsetCandidate_eventually_log_gap hα0 hα1 δ hLsq u hu).mono
      fun x hx _ => hx
  · exact Filter.Eventually.of_forall fun _ hx => (hu hx).elim

def shellOffset {D q L : ℕ} (t : Fin D → ℕ) (hLq : L ≤ q)
    (hwide : tupleInWindow q L t) : Fin D → Fin (2 * L + 1) :=
  fun i => ⟨t i - (q - L), by
    have hlo := (hwide i).1
    have hhi := (hwide i).2
    omega⟩

lemma shellOffset_add_base {D q L : ℕ} (t : Fin D → ℕ) (hLq : L ≤ q)
    (hwide : tupleInWindow q L t) (i : Fin D) :
    q - L + (shellOffset t hLq hwide i : ℕ) = t i := by
  have hlo := (hwide i).1
  simp only [shellOffset]
  omega

lemma shellOffset_sum {D q L : ℕ} (t : Fin D → ℕ) (hLq : L ≤ q)
    (hwide : tupleInWindow q L t) :
    (∑ i, (shellOffset t hLq hwide i : ℕ)) =
      (∑ i, t i) - D * (q - L) := by
  have hlo : ∀ i ∈ (Finset.univ : Finset (Fin D)), q - L ≤ t i := by
    intro i _
    have := (hwide i).1
    omega
  simp only [shellOffset]
  calc
    (∑ x, (t x - (q - L))) = ∑ x ∈ (Finset.univ : Finset (Fin D)),
        (t x - (q - L)) := by simp
    _ = (∑ x ∈ (Finset.univ : Finset (Fin D)), t x) -
        ∑ x ∈ (Finset.univ : Finset (Fin D)), (q - L) :=
      Finset.sum_tsub_distrib Finset.univ hlo
    _ = (∑ i, t i) - D * (q - L) := by simp

lemma shellOffset_boundaryCandidate {D q K : ℕ} (δ t : Fin D → ℕ)
    (hLq : K + 1 ≤ q)
    (hwide : tupleInWindow q (K + 1) t)
    (hout : ¬ tupleInWindow q K t)
    (hsum : D * q + (∑ i, δ i) ≤ ∑ i, t i) :
    boundaryOffsetCandidate δ (shellOffset t hLq hwide) := by
  let L := K + 1
  have hsumOffset := shellOffset_sum t hLq hwide
  have hleft : (∑ i, (δ i + L)) = (∑ i, δ i) + D * L := by
    simp [L, Finset.sum_add_distrib]
  have hcandidateSum : (∑ i, (δ i + L)) ≤
      ∑ i, (shellOffset t hLq hwide i : ℕ) := by
    rw [hleft, hsumOffset]
    have hqsplit : q = (q - L) + L := by omega
    apply Nat.le_sub_of_add_le
    calc
      (∑ i, δ i) + D * L + D * (q - L) =
          (∑ i, δ i) + D * (L + (q - L)) := by ring
      _ = (∑ i, δ i) + D * q := by rw [Nat.add_comm L (q - L), ← hqsplit]
      _ = D * q + (∑ i, δ i) := by omega
      _ ≤ ∑ i, t i := hsum
  refine ⟨hcandidateSum, ?_⟩
  rw [tupleInWindow] at hout
  obtain ⟨i, hi⟩ := not_forall.mp hout
  by_cases hiLow : q ≤ t i + K
  · have hiHigh : ¬ t i ≤ q + K := fun h => hi ⟨hiLow, h⟩
    refine ⟨i, Or.inr ?_⟩
    simp only [shellOffset]
    have hwideHigh := (hwide i).2
    omega
  · refine ⟨i, Or.inl ?_⟩
    simp only [shellOffset]
    have hwideLow := (hwide i).1
    omega

lemma tupleStretchedValuation_shellOffset {α : ℝ} {D q L : ℕ}
    (t : Fin D → ℕ) (hLq : L ≤ q) (hwide : tupleInWindow q L t) :
    tupleStretchedValuation α t =
      ∑ i, stretchedExp α ((q - L : ℕ) + (shellOffset t hLq hwide i : ℕ)) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact_mod_cast (shellOffset_add_base t hLq hwide i).symm

lemma tupleStretchedValuation_witness_as_offset {α : ℝ} {D q L : ℕ}
    (δ : Fin D → ℕ) (hLq : L ≤ q) :
    tupleStretchedValuation α (fun i => q + δ i) =
      ∑ i, stretchedExp α ((q - L : ℕ) + (δ i + L)) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hnat : q - L + (δ i + L) = q + δ i := by omega
  exact_mod_cast hnat.symm

lemma stretchedFiniteDifference_shellOffset_eq {α : ℝ} {D q L : ℕ}
    (δ t : Fin D → ℕ) (hLq : L ≤ q) (hwide : tupleInWindow q L t) :
    stretchedFiniteDifference α
        (tupleDifference (fun i => (shellOffset t hLq hwide i : ℕ))
          (fun i => δ i + L)) ((q : ℝ) - L) =
      tupleStretchedValuation α t -
        tupleStretchedValuation α (fun i => q + δ i) := by
  rw [stretchedFiniteDifference_tupleDifference]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hnat := shellOffset_add_base t hLq hwide i
    have hcast : ((q - L + (shellOffset t hLq hwide i : ℕ) : ℕ) : ℝ) =
        (t i : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    rw [Nat.cast_sub hLq] at hcast
    exact hcast
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    have hq : (q : ℝ) - L + (δ i + L : ℕ) = (q : ℝ) + δ i := by
      push_cast
      ring
    simpa only [Nat.cast_add] using hq

/-- Eventual bounded confinement for every least-shift collection containing a fixed-offset
witness.  The collection may vary arbitrarily with `q`; only its fixed arity and fixed source-sum
window are used. -/
theorem exists_eventually_bounded_stretchedMinimizer {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {D : ℕ} (hD : 0 < D)
    (δ : Fin D → ℕ) (C : ℕ) :
    ∃ K : ℕ, ∀ᶠ q : ℕ in atTop,
      ∀ (A : Finset (Fin D → ℕ)),
        (fun i => q + δ i) ∈ A →
        (∀ s ∈ A,
          D * q + (∑ i, δ i) ≤ ∑ i, s i ∧
          (∑ i, s i) ≤ D * q + (∑ i, δ i) + C) →
        ∀ s ∈ A,
          (∀ r ∈ A,
            tupleStretchedValuation α s ≤ tupleStretchedValuation α r) →
          tupleInWindow q K s := by
  classical
  let Aδ := ∑ i, δ i
  let Sδ := ∑ i, (δ i) ^ 2
  let K := C + Aδ + Sδ + 1
  let L := K + 1
  have hCtotK : Aδ + C < K := by
    dsimp [K]
    omega
  have hLpos : 0 < L := by dsimp [L, K]; omega
  have hSltL : Sδ < L := by dsimp [L, K]; omega
  have hSltLsq : Sδ < L ^ 2 := by
    exact hSltL.trans_le (by nlinarith : L ≤ L ^ 2)
  have hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2 := by
    have hcast : (Sδ : ℝ) < (L : ℝ) ^ 2 := by exact_mod_cast hSltLsq
    simpa [Sδ] using hcast
  obtain ⟨Q, hrecord⟩ := exists_stretchedIncrement_record_strict hα0 hα1
  have hgapReal := boundaryOffsetCandidate_eventually_all_log_gap hα0 hα1 δ hLsq
  have hbaseT : Tendsto (fun q : ℕ => (q : ℝ) - L) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(L : ℝ)) tendsto_natCast_atTop_atTop
  have hgapNat : ∀ᶠ q : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u → Real.log ((q : ℝ) - L) <
        stretchedFiniteDifference α
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L))
          ((q : ℝ) - L) := hbaseT.eventually hgapReal
  refine ⟨K, ?_⟩
  filter_upwards [hgapNat, eventually_ge_atTop (max (L + 2) (Q + 1))] with q hgap hq
  intro A hwitness hbounds s hs hmin
  by_contra hout
  have hLq : L ≤ q := by omega
  have hqQ : Q + 1 ≤ q := by omega
  have hsBounds := hbounds s hs
  have hsumLower0 : D * q ≤ ∑ i, s i := by
    exact (Nat.le_add_right _ Aδ).trans (by simpa [Aδ] using hsBounds.1)
  have hsumUpper0 : (∑ i, s i) ≤ D * q + (Aδ + C) := by
    simpa [Aδ, Nat.add_assoc] using hsBounds.2
  obtain ⟨t, htsum, htwide, htout, htval⟩ :=
    exists_boundaryShell_of_sum_bounds hD hCtotK hqQ hrecord s
      hsumLower0 hsumUpper0 hout
  have htsumLower : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
    rw [htsum]
    exact hsBounds.1
  have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumLower
  have hgap' := hgap (shellOffset t hLq htwide) hcand
  rw [stretchedFiniteDifference_shellOffset_eq δ t hLq htwide] at hgap'
  have hlogPos : 0 < Real.log ((q : ℝ) - L) := by
    apply Real.log_pos
    norm_cast
    omega
  have hwitLt : tupleStretchedValuation α (fun i => q + δ i) <
      tupleStretchedValuation α t := by
    linarith
  have hminW := hmin (fun i => q + δ i) hwitness
  linarith

end

end GaloisForLFunctions
