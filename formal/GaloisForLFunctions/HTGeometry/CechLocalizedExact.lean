import GaloisForLFunctions.HTGeometry.FinsetCechDatum

/-!
# Čech exactness from local contractions

Let a commutative ring `R` act linearly on a Čech datum `D` and let `g : T → R` generate the unit
ideal.  Suppose that, along each enlargement `s ⊆ s ∪ {k}`, the restriction behaves like the
localization map inverting `g k`:

* (a) every section over `s ∪ {k}` becomes a restriction from `s` after multiplication by a power
  of `g k`;
* (b) a section over `s` whose restriction to `s ∪ {k}` vanishes is killed by a power of `g k`.

Then the augmented Čech complex of `D` is exact in every degree.  For each `k` the cone operator of
`k`, made integral by (a), contracts `g k ^ N` times a cocycle up to an error which restricts to zero
and is therefore killed by a further power of `g k` by (b); the powers of the `g k` generate the
unit ideal, so the cocycle itself is a coboundary.  This is the algebraic content of Serre's
vanishing theorem for the structure sheaf of an affine scheme, where `D` is the Čech datum of a
cover by basic open sets.

* `HTGeometry.FinsetCechDatum.exists_d_eq_pow_smul` : the local contraction.
* `HTGeometry.FinsetCechDatum.exactAt_of_localized` : exactness.
-/

namespace HTGeometry

namespace FinsetCechDatum

open GaloisForLFunctions.HTGeometry.BorelWeil

universe v

variable {T : Type*} [DecidableEq T] [LinearOrder T] [Fintype T] (D : FinsetCechDatum.{v} T)
  {R : Type*} [CommRing R] [∀ s, Module R (D.obj s)]

omit [Fintype T] in
/-- The differential is linear over a ring acting compatibly with restriction. -/
theorem d_smul
    (hres : ∀ {s t : Finset T} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (r : R) (c : D.Cochain) : D.d (r • c) = r • D.d c := by
  funext s
  simp only [d, Pi.smul_apply, Finset.smul_sum, hres]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

/-- **The local contraction.**  For a fixed index `k`, a power of `g k` times a cocycle is a
coboundary. -/
theorem exists_d_eq_pow_smul
    (hres : ∀ {s t : Finset T} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (a : R)
    (ha : ∀ (s : Finset T) (y : D.obj (insert k s)), ∃ (n : ℕ) (x : D.obj s),
      D.res (Finset.subset_insert k s) x = a ^ n • y)
    (hb : ∀ (s : Finset T) (x : D.obj s), D.res (Finset.subset_insert k s) x = 0 →
      ∃ n : ℕ, a ^ n • x = 0)
    {p : ℕ} {c : D.Cochain} (hc : D.IsDeg c p) (hdc : D.d c = 0) :
    ∃ (N : ℕ) (b : D.Cochain), (∀ s : Finset T, s.card ≠ p → b s = 0) ∧ D.d b = a ^ N • c := by
  classical
  -- integral lifts of the cone values
  choose n x hx using fun t : Finset T => ha t (c (insert k t))
  set N₁ := (Finset.univ : Finset (Finset T)).sup n with hN₁
  have hn : ∀ t, n t ≤ N₁ := fun t => Finset.le_sup (Finset.mem_univ t)
  let x' : ∀ t : Finset T, D.obj t := fun t => a ^ (N₁ - n t) • x t
  have hx' : ∀ t, D.res (Finset.subset_insert k t) (x' t) = a ^ N₁ • c (insert k t) := by
    intro t
    rw [hres, hx, smul_smul, ← pow_add, Nat.sub_add_cancel (hn t)]
  let b : D.Cochain := fun t =>
    if k ∈ t then 0 else if t.card = p then (cechSign (insert k t) k : ℤ) • x' t else 0
  have hb0 : ∀ t : Finset T, t.card ≠ p → b t = 0 := by
    intro t ht
    change (if k ∈ t then 0 else if t.card = p then _ else 0) = 0
    split_ifs <;> rfl
  -- the error restricts to zero
  have herr : ∀ s : Finset T,
      D.res (Finset.subset_insert k s) (D.d b s - a ^ N₁ • c s) = 0 := by
    intro s
    by_cases hs : s.card = p + 1
    · set s' := insert k s with hs'
      have hss' : s ⊆ s' := Finset.subset_insert k s
      have hpull : ∀ u ∈ s, D.pull b s' (s.erase u)
          = a ^ N₁ • cechHModule ℤ k (D.pull c s') (s.erase u) := by
        intro u hu
        have hts : s.erase u ⊆ s' := (Finset.erase_subset u s).trans hss'
        rw [D.pull_of_subset b hts, cechHModule]
        by_cases hk : k ∈ s.erase u
        · rw [if_pos hk, smul_zero]
          change D.res hts (if k ∈ s.erase u then 0 else _) = 0
          rw [if_pos hk, map_zero]
        · rw [if_neg hk]
          have hcard : (s.erase u).card = p := by
            rw [Finset.card_erase_of_mem hu, hs]; rfl
          change D.res hts (if k ∈ s.erase u then 0 else
            if (s.erase u).card = p then (cechSign (insert k (s.erase u)) k : ℤ) • x' _ else 0) = _
          rw [if_neg hk, if_pos hcard, map_zsmul,
            ← D.res_res (Finset.subset_insert k (s.erase u))
              (Finset.insert_subset_insert k (Finset.erase_subset u s)), hx', hres,
            ← D.pull_of_subset c (Finset.insert_subset_insert k (Finset.erase_subset u s)),
            smul_comm]
      have hdb : D.res hss' (D.d b s) = a ^ N₁ • D.res hss' (c s) := by
        rw [D.res_d b hss', cechDModule]
        rw [Finset.sum_congr rfl fun u hu => by rw [hpull u hu]]
        have hid := cechDModule_cechHModule_add ℤ k (D.pull c s') s
        have hzero : cechHModule ℤ k (cechDModule ℤ (D.pull c s')) s = 0 := by
          rw [cechHModule]
          split_ifs with hks
          · rfl
          · rw [← D.res_d c (Finset.Subset.refl _), hdc]
            simp
        rw [hzero, add_zero, cechDModule] at hid
        rw [← D.pull_of_subset c hss', ← hid, Finset.smul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [smul_comm]
      rw [map_sub, hdb, hres, sub_self]
    · rw [D.d_eq_zero_of_card hb0 s hs, hc s hs, smul_zero, sub_zero, map_zero]
  -- kill the error by a further power
  choose m hm using fun s : Finset T => hb s _ (herr s)
  set M := (Finset.univ : Finset (Finset T)).sup m with hM
  have hm' : ∀ s, m s ≤ M := fun s => Finset.le_sup (Finset.mem_univ s)
  refine ⟨M + N₁, a ^ M • b, fun t ht => by rw [Pi.smul_apply, hb0 t ht, smul_zero], ?_⟩
  rw [D.d_smul hres]
  funext s
  have hkill : a ^ M • (D.d b s - a ^ N₁ • c s) = 0 := by
    rw [← Nat.sub_add_cancel (hm' s), pow_add, mul_smul, hm s, smul_zero]
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hkill
  rw [Pi.smul_apply, Pi.smul_apply, hkill]

/-- **Exactness from local contractions.**  If a ring acting compatibly on a Čech datum contains
elements `g k` generating the unit ideal such that each enlargement `s ⊆ s ∪ {k}` behaves like
inverting `g k`, then the augmented Čech complex is exact in every degree. -/
theorem exactAt_of_localized
    (hres : ∀ {s t : Finset T} (h : s ⊆ t) (r : R) (x : D.obj s), D.res h (r • x) = r • D.res h x)
    (g : T → R) (hg : Ideal.span (Set.range g) = ⊤)
    (ha : ∀ (k : T) (s : Finset T) (y : D.obj (insert k s)), ∃ (n : ℕ) (x : D.obj s),
      D.res (Finset.subset_insert k s) x = g k ^ n • y)
    (hb : ∀ (k : T) (s : Finset T) (x : D.obj s), D.res (Finset.subset_insert k s) x = 0 →
      ∃ n : ℕ, g k ^ n • x = 0)
    (p : ℕ) : D.ExactAt p := by
  classical
  intro c hc hdc
  choose N b hb hdb using fun k : T =>
    D.exists_d_eq_pow_smul (k := k) hres (g k) (ha k) (hb k) hc hdc
  set N' := (Finset.univ : Finset T).sup N with hN'
  have hN : ∀ k, N k ≤ N' := fun k => Finset.le_sup (Finset.mem_univ k)
  have hdb' : ∀ k, D.d (g k ^ (N' - N k) • b k) = g k ^ N' • c := by
    intro k
    rw [D.d_smul hres, hdb, smul_smul, ← pow_add, Nat.sub_add_cancel (hN k)]
  have hspan : Ideal.span (Set.range fun k => g k ^ N') = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N'
    rwa [← Set.range_comp] at this
  have h1 : (1 : R) ∈ Submodule.span R (Set.range fun k => g k ^ N') := by
    change (1 : R) ∈ Ideal.span _
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h1
  refine ⟨∑ k, e k • (g k ^ (N' - N k) • b k), fun s hs => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, hb k s hs, smul_zero, smul_zero]
  · change D.dHom (∑ k, e k • (g k ^ (N' - N k) • b k)) = c
    rw [map_sum]
    change ∑ k, D.d (e k • (g k ^ (N' - N k) • b k)) = c
    rw [Finset.sum_congr rfl fun k _ => by rw [D.d_smul hres, hdb', smul_smul], ← Finset.sum_smul]
    simp only [smul_eq_mul] at he
    rw [he, one_smul]

end FinsetCechDatum

end HTGeometry
