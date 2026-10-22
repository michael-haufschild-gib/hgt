import GaloisForLFunctions.RHTower.Deninger.DeningerDeterminantalLaplace
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCanonicity
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Hazewinkel Hankel ideals and infinitesimal descent

This module formalizes Deninger's Lemma 2.2 and Proposition 2.1(c,d) for Hazewinkel's
ind-scheme of finite-Hankel-rank big Witt vectors.  It specializes generalized Laplace
containment to the universal Hankel matrix and proves nilpotent-kernel rank descent.

All statements hold over arbitrary commutative rings.  Nilpotents are retained; no
reducedness, torsion-freeness, or characteristic-zero premise enters the proofs.
-/

namespace RHTower

noncomputable section

def deningerHazewinkelUniversalCoeff : ℕ → MvPolynomial ℕ ℤ
  | 0 => 1
  | n + 1 => MvPolynomial.X n

def deningerHazewinkelUniversalHankel : Matrix ℕ ℕ (MvPolynomial ℕ ℤ) :=
  fun i j => deningerHazewinkelUniversalCoeff (i + j)

def deningerHazewinkelIdeal (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) :=
  deningerMatrixMinorIdeal (n + 1) deningerHazewinkelUniversalHankel

theorem deningerHazewinkelIdeal_mul_sub_one_le_pow
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    deningerHazewinkelIdeal (n * k - 1) ≤
      (deningerHazewinkelIdeal (n - 1)) ^ k := by
  unfold deningerHazewinkelIdeal
  have hnk : 1 ≤ n * k := Nat.mul_pos (by omega) (by omega)
  rw [Nat.sub_add_cancel hnk,
    Nat.sub_add_cancel (by omega : 1 ≤ n)]
  exact deningerMatrixMinorIdeal_mul_le_pow n k deningerHazewinkelUniversalHankel

def deningerBigWittHankel {A : Type*} [CommRing A]
    (w : DeningerBigWittAdditive A) : Matrix ℕ ℕ A :=
  fun i j => PowerSeries.coeff (i + j) (deningerBigWittSeries w)

def DeningerBigWittHankelRankLT {A : Type*} [CommRing A]
    (n : ℕ) (w : DeningerBigWittAdditive A) : Prop :=
  ∀ rows cols : Fin n → ℕ,
    ((deningerBigWittHankel w).submatrix rows cols).det = 0

def DeningerBigWittFiniteHankelRank {A : Type*} [CommRing A]
    (w : DeningerBigWittAdditive A) : Prop :=
  ∃ n : ℕ, DeningerBigWittHankelRankLT n w

@[simp] theorem deningerBigWittHankel_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (w : DeningerBigWittAdditive A) :
    deningerBigWittHankel (deningerBigWittMap f w) =
      fun i j => f (deningerBigWittHankel w i j) := by
  ext i j
  simp [deningerBigWittHankel, deningerBigWittSeries_map,
    PowerSeries.coeff_map]

theorem DeningerBigWittHankelRankLT.map
    {A B : Type*} [CommRing A] [CommRing B]
    {n : ℕ} {w : DeningerBigWittAdditive A}
    (h : DeningerBigWittHankelRankLT n w) (f : A →+* B) :
    DeningerBigWittHankelRankLT n (deningerBigWittMap f w) := by
  intro rows cols
  have hm := congrArg f (h rows cols)
  rw [map_zero, f.map_det] at hm
  have heq : f.mapMatrix ((deningerBigWittHankel w).submatrix rows cols) =
      (deningerBigWittHankel (deningerBigWittMap f w)).submatrix rows cols := by
    ext i j
    simp [deningerBigWittHankel_map, Matrix.submatrix_apply]
  rwa [heq] at hm

theorem deningerBigWittMinorIdeal_le_ker_of_rankLT_map
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (w : DeningerBigWittAdditive A)
    (h : DeningerBigWittHankelRankLT n (deningerBigWittMap f w)) :
    deningerMatrixMinorIdeal n (deningerBigWittHankel w) ≤ RingHom.ker f := by
  rw [deningerMatrixMinorIdeal, Ideal.span_le]
  rintro x ⟨rows, cols, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [f.map_det]
  have heq : f.mapMatrix ((deningerBigWittHankel w).submatrix rows cols) =
      (deningerBigWittHankel (deningerBigWittMap f w)).submatrix rows cols := by
    ext i j
    simp [deningerBigWittHankel_map, Matrix.submatrix_apply]
  rw [heq]
  exact h rows cols

theorem DeningerBigWittHankelRankLT.of_map_of_ker_pow_eq_bot
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n k : ℕ) (w : DeningerBigWittAdditive A)
    (hker : (RingHom.ker f) ^ k = ⊥)
    (h : DeningerBigWittHankelRankLT n (deningerBigWittMap f w)) :
    DeningerBigWittHankelRankLT (n * k) w := by
  intro rows cols
  have hminor : ((deningerBigWittHankel w).submatrix rows cols).det ∈
      deningerMatrixMinorIdeal (n * k) (deningerBigWittHankel w) :=
    deningerMatrixMinorDet_mem (n * k) (deningerBigWittHankel w) rows cols
  have hpower : ((deningerBigWittHankel w).submatrix rows cols).det ∈
      (deningerMatrixMinorIdeal n (deningerBigWittHankel w)) ^ k :=
    deningerMatrixMinorIdeal_mul_le_pow n k (deningerBigWittHankel w) hminor
  have hle := deningerBigWittMinorIdeal_le_ker_of_rankLT_map f n w h
  have hzero : ((deningerBigWittHankel w).submatrix rows cols).det ∈
      (⊥ : Ideal A) := by
    rw [← hker]
    exact Ideal.pow_right_mono hle k hpower
  simpa using hzero

theorem deningerBigWittFiniteHankelRank_map_iff_of_ker_nilpotent
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (k : ℕ) (hker : (RingHom.ker f) ^ k = ⊥)
    (w : DeningerBigWittAdditive A) :
    DeningerBigWittFiniteHankelRank (deningerBigWittMap f w) ↔
      DeningerBigWittFiniteHankelRank w := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n * k, hn.of_map_of_ker_pow_eq_bot f n k w hker⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.map f⟩

theorem DeningerBigWittFiniteHankelRank.map
    {A B : Type*} [CommRing A] [CommRing B]
    {w : DeningerBigWittAdditive A}
    (h : DeningerBigWittFiniteHankelRank w) (f : A →+* B) :
    DeningerBigWittFiniteHankelRank (deningerBigWittMap f w) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.map f⟩

abbrev DeningerHazewinkelWitt (A : Type*) [CommRing A] :=
  {w : DeningerBigWittAdditive A // DeningerBigWittFiniteHankelRank w}

def deningerHazewinkelWittMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerHazewinkelWitt A → DeningerHazewinkelWitt B :=
  fun w => ⟨deningerBigWittMap f w.1, w.2.map f⟩

theorem deningerHazewinkelWitt_infinitesimal_cartesian
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (k : ℕ) (hker : (RingHom.ker f) ^ k = ⊥)
    (w : DeningerBigWittAdditive A) :
    DeningerBigWittFiniteHankelRank (deningerBigWittMap f w) ↔
      ∃ u : DeningerHazewinkelWitt A, u.1 = w := by
  rw [deningerBigWittFiniteHankelRank_map_iff_of_ker_nilpotent f k hker]
  constructor
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact u.2

theorem deningerHazewinkelWitt_formally_etale_unique_lift
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (k : ℕ) (hker : (RingHom.ker f) ^ k = ⊥)
    (w : DeningerBigWittAdditive A) (v : DeningerHazewinkelWitt B)
    (hmap : deningerBigWittMap f w = v.1) :
    ∃! u : DeningerHazewinkelWitt A,
      u.1 = w ∧ deningerHazewinkelWittMap f u = v := by
  have hfiniteMap : DeningerBigWittFiniteHankelRank
      (deningerBigWittMap f w) := hmap ▸ v.2
  have hfinite : DeningerBigWittFiniteHankelRank w :=
    (deningerBigWittFiniteHankelRank_map_iff_of_ker_nilpotent
      f k hker w).mp hfiniteMap
  let u : DeningerHazewinkelWitt A := ⟨w, hfinite⟩
  refine ⟨u, ?_, ?_⟩
  · constructor
    · rfl
    · apply Subtype.ext
      exact hmap
  · intro u' hu'
    apply Subtype.ext
    exact hu'.1

theorem deningerBigWittMap_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (deningerBigWittMap f) := by
  intro w
  choose a ha using fun n : ℕ => hf
    (PowerSeries.coeff (n + 1) (deningerBigWittSeries w))
  let coeff : ℕ → A
    | 0 => 1
    | n + 1 => a n
  let F : PowerSeries A := PowerSeries.mk coeff
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [F, coeff]
  let u := deningerBigWittOfSeries F hF0
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map f F = deningerBigWittSeries w
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_map]
      simp [F, coeff, PowerSeries.coeff_zero_eq_constantCoeff,
        deningerBigWittSeries_constantCoeff]
  | succ n =>
      rw [PowerSeries.coeff_map]
      simpa [F, coeff] using ha n

theorem deningerHazewinkelWitt_formally_smooth
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    (k : ℕ) (hker : (RingHom.ker f) ^ k = ⊥) :
    Function.Surjective (deningerHazewinkelWittMap f) := by
  intro v
  obtain ⟨w, hw⟩ := deningerBigWittMap_surjective f hf v.1
  have hfiniteMap : DeningerBigWittFiniteHankelRank
      (deningerBigWittMap f w) := hw ▸ v.2
  have hfinite : DeningerBigWittFiniteHankelRank w :=
    (deningerBigWittFiniteHankelRank_map_iff_of_ker_nilpotent
      f k hker w).mp hfiniteMap
  refine ⟨⟨w, hfinite⟩, ?_⟩
  apply Subtype.ext
  exact hw

end

end RHTower
