import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Lattice
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.YonedaULift

section
/-
This section contains some of the lemmas about `Fin`.
Should be moved to somewhere else in the end.
-/
namespace Fin

variable {m n k : ℕ}

lemma le_image_of_StrictMono {f : Fin m → Fin n} (hf : StrictMono f) (i : Fin m) :
(i : ℕ) ≤ f i  := by
  obtain ⟨i, hi⟩ := i
  simp
  induction i with
  | zero => simp
  | succ n hn =>
      calc n + 1 ≤ f ⟨n, (Nat.lt_succ_self n).trans hi⟩ + 1 := by simp [hn]
      _ ≤ f ⟨n+1, hi⟩ := by
        rw [Nat.add_one_le_iff, ← Fin.lt_def]
        exact hf (by simp only [Fin.mk_lt_mk, Nat.lt_succ_self])

lemma StrictMono.le {f : Fin m → Fin n} (hf : StrictMono f) :
    m ≤ n := by
  cases m with
  | zero => simp
  | succ m =>
      rw [Nat.succ_le_iff]
      apply lt_of_le_of_lt (Fin.le_image_of_StrictMono hf (Fin.last _)) (is_lt _)

lemma Monotone.exists_eq_of_le {f : Fin (m + 1) → Fin n} (hf : Monotone f) :
    n ≤ m → ∃ i : Fin m, f i.castSucc = f i.succ := by
  intro h; contrapose! h
  apply StrictMono.le (hf.strictMono_of_injective (injective_of_lt_imp_ne _))
  intro i j hij
  apply (lt_of_lt_of_le
    ((hf (castSucc_lt_succ i).le).lt_of_ne (h <| i.castPred (ne_last_of_lt hij)))
    (hf (castSucc_lt_iff_succ_le.mp hij))).ne

open Set
lemma range_succAbove_succAbove_of_castSucc_lt (i : Fin (n + 1)) (j : Fin (n + 2))
  (hij : i.castSucc < j) :
    range (j.succAbove ∘ i.succAbove) = {i.castSucc, j}ᶜ := by
  simp only [range_comp, range_succAbove, compl_eq_univ_diff,
             image_diff succAbove_right_injective, image_univ,
             range_succAbove, image_singleton, diff_diff,
             union_comm {j}]
  congr
  rw [succAbove_of_castSucc_lt _ _ hij]

noncomputable def factor_of_range_subset (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m)
  (h : range g ⊆ range f) :
    Fin k →o Fin (n + 1) where
  toFun i := sSup {j | f j = g i}
  monotone' i j hij := by
    rcases eq_or_lt_of_le (g.monotone hij) with hij | hij
    simp only [hij]; apply le_refl
    simp only [mem_setOf_eq]
    apply sSup_le_sSup_of_forall_exists_le
    intro l hl
    obtain ⟨l', hl'⟩ := h ⟨j, rfl⟩
    exact ⟨l', hl', (f.monotone.reflect_lt (hl'.symm ▸ hl.symm ▸ hij)).le⟩

lemma factor_of_range_subset_spec (f : Fin (n + 1) →o Fin m) (g : Fin k →o Fin m) (h : range g ⊆ range f) :
    g = f ∘ factor_of_range_subset f g h := by
  ext i : 1
  simp [factor_of_range_subset]
  have : sSup {j | f j = g i} ∈ {j | f j = g i} := by
    apply Nonempty.csSup_mem
    exact h ⟨i, rfl⟩
    rw [← finite_coe_iff]
    apply Subtype.finite
  exact this.symm

lemma exists_OrderHom_comp_iff_range_subset {n m k} (f : Fin n →o Fin m) (g : Fin k →o Fin m) :
    (∃ h : Fin k →o Fin n, g = f ∘ h) ↔ range g ⊆ range f := by
  constructor
  . rw [range_subset_range_iff_exists_comp]
    exact fun ⟨h, hh⟩ ↦ ⟨⇑h, hh⟩
  . cases n with
  | zero =>
      cases k with
      | zero => intro; use OrderHom.id; ext i; exact i.elim0
      | succ => rw [Set.range_eq_empty f]; intro h; apply False.elim $ h ⟨0, rfl⟩
  | succ n =>
      intro h
      exact ⟨factor_of_range_subset f g h, factor_of_range_subset_spec _ _ h⟩

end Fin
end

open CategoryTheory Simplicial Limits SimplexCategory Function Opposite Classical SSet
  standardSimplex Set Fin

section
namespace SSet
variable {n m : ℕ}

@[simp]
lemma asOrderHom_objMk (x : Fin (n + 1) →o Fin (m + 1)) :
  asOrderHom (objMk x) = x := rfl

@[ext]
lemma standardSimplex.ext {n : SimplexCategoryᵒᵖ} (x y : Δ[m].obj n)
  (h : asOrderHom x = asOrderHom y) :
    x = y := by
  apply_fun objEquiv _ _
  ext : 1; exact h

def recop {F : SimplexCategoryᵒᵖ → Sort*} (h : ∀ n : ℕ, F (op [n])) :
    ∀ X, F X := fun n =>
  h n.unop.len

lemma exists_eq_standardSimplex_map (f : Δ[m] ⟶ Δ[n]) :
    ∃ l : SimplexCategory.mk m ⟶ [n], f = standardSimplex.map l := by
  use objEquiv _ _ (yonedaEquiv _ _ f)
  exact ((yonedaEquiv _ _).left_inv _).symm

end SSet
end

section Degenerate

namespace SSet

variable {X : SSet} {n k: ℕ} (x : X _[n])

def Degenerate : {n : ℕ} → (x : X _[n]) → Prop
| 0, _ => False
| _ + 1, x => ∃ i, x ∈ range (X.map (σ i).op)

@[simp]
def Nondegenerate : Prop := ¬ Degenerate x

@[simp]
lemma Degenerate.vertice (x : X _[0]) :
  ¬ Degenerate x := by simp only [Degenerate, not_false_eq_true]

lemma Degenerate.eq_zero {x : X _[k]} : k = 0 → ¬ Degenerate x := by
  cases k; simp; simp

@[simp]
lemma Degenerate.succ {x : X _[n + 1]} :
  Degenerate x ↔ ∃ i, x ∈ range (X.map (σ i).op) := by simp only [Degenerate]

def Degenerates (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Degenerate x}

def Nondegenerates (X : SSet) := { ⟨_, x⟩ : Σ n : ℕ, X _[n] | Nondegenerate x}

lemma degenerate_iff_mem_range :
    Degenerate x ↔
  ∃ m, ∃ φ : ([n] : SimplexCategory) ⟶ [m], m < n ∧ x ∈ range (X.map φ.op) := by
  cases n with
  | zero => simp
  | succ n =>
    constructor
    . rintro ⟨i, hi⟩
      exact ⟨n, ⟨σ i, ⟨by norm_num, hi⟩⟩⟩
    . rintro ⟨m, ⟨φ, ⟨h₁, ⟨y, hy⟩⟩⟩⟩
      obtain ⟨i, hi⟩ :
        ∃ i : Fin (n + 1), φ.toOrderHom i.castSucc = φ.toOrderHom i.succ := by
          apply Monotone.exists_eq_of_le φ.toOrderHom.monotone'
          norm_num; rwa [← Nat.lt_succ_iff]
      have : φ = (σ i) ≫ (δ i.castSucc) ≫ φ := by
        ext j; simp [δ, σ]
        by_cases hj : j < i.castSucc
        . congr
          rw [succAbove_castSucc_of_lt _ _ (by
              rwa [predAbove_of_le_castSucc _ _ hj.le, castPred_lt_iff]),
            predAbove_of_lt_succ _ _ (hj.trans (castSucc_lt_succ _)),
            castSucc_castPred _ (ne_last_of_lt hj)]
        . by_cases hj' : j = i.castSucc
          . simp only [hj', predAbove_castSucc_self, succAbove_castSucc_self]
            congr 1
          . simp only [not_lt] at hj
            have hj := lt_of_le_of_ne hj (by rwa [eq_comm] at hj')
            congr
            rw [predAbove_of_castSucc_lt _ _ hj, succAbove_of_le_castSucc _ _ (by
                simpa only [castSucc_le_castSucc_iff, Fin.le_pred_iff]),
              succ_pred]
      use i
      rw [this] at hy
      simp only [op_comp, Category.assoc, FunctorToTypes.map_comp_apply] at hy
      exact ⟨_, hy⟩

variable {X : SSet} {n : ℕ} (x : X _[n])

lemma Degenerate.iff_exists_asOrderHom (x : Δ[n] _[k]) :
  Degenerate x ↔ ∃ i : Fin k, asOrderHom x i.castSucc = asOrderHom x i.succ := by
  cases k with
  | zero => simp only [Degenerate.vertice, IsEmpty.exists_iff]
  | succ k =>
      constructor
      . rintro ⟨i, ⟨y, hy⟩⟩
        use i
        simp [← hy]
        have (j : Fin _): (asOrderHom (Δ[n].map (σ i).op y)) j
          = (asOrderHom y) ((σ i).toOrderHom j):= rfl -- okay...
        erw [this i.castSucc, this i.succ]
        congr 1
        simp [σ]
      . intro h
        obtain ⟨i, hi⟩ := h
        use i, (Δ[n].map (δ i).op x)
        apply_fun (objEquiv _ _)
        ext j; simp [map_apply, δ, σ]
        by_cases hj : j = i.castSucc
        . simp [hj]; congr 1
          convert hi.symm
        . rw [succAbove_predAbove hj]

-- can be simplified now
lemma Nondegenerate.iff_StrictMono (x : Δ[n] _[k]) :
  Nondegenerate x ↔ StrictMono (asOrderHom x) := by
  cases k with
  | zero => simp; intro i j h; simp [Subsingleton.allEq i j] at h
  | succ k =>
      simp only [Nondegenerate, Degenerate.iff_exists_asOrderHom, not_exists]
      constructor
      . intro h i j hij
        apply ((asOrderHom x).monotone' hij.le).lt_of_ne
        contrapose! h
        use ⟨i.1, val_lt_last (ne_last_of_lt hij)⟩
        apply le_antisymm ((asOrderHom x).monotone' (Fin.castSucc_lt_succ _).le)
        simp only [succ_mk, castSucc_mk, h]
        apply (asOrderHom x).monotone'
          <| le_iff_val_le_val.mp (Nat.succ_le_of_lt (lt_iff_val_lt_val.mp hij))
      . intro h _
        apply h.injective.ne (castSucc_lt_succ _).ne

lemma Nondegenerate.iff_injective (x : Δ[n] _[k]) :
  Nondegenerate x ↔ Injective (asOrderHom x) := by
  cases k with
  | zero => simp [Injective]; intros; apply Subsingleton.allEq
  | succ k =>
      rw [Nondegenerate.iff_StrictMono]
      apply (asOrderHom x).monotone'.strictMono_iff_injective

lemma Nondegenerate.le (x : Δ[n] _[k]) : Nondegenerate x → k ≤ n := by
  intro h
  cases k with
  | zero => simp
  | succ k =>
    rw [Nondegenerate.iff_StrictMono] at h
    apply le_trans (Fin.le_image_of_StrictMono h (last _)) (Nat.lt_succ.mp (is_lt _))

lemma Nondegenerate.of_lt (x : Δ[n] _[k]) : n < k → Degenerate x := by
  rw [← not_imp_not, not_lt]
  apply le

end SSet
end Degenerate

section

lemma exists_and_of_transitive_of_reflexive (f : ℕ → Type*) (P : {n : ℕ} → f n → Prop)
  (R : (n : ℕ) × f n → (n : ℕ) × f n → Prop)
  (hR : Transitive R) (hR' : Reflexive R) (h₀ : ∀ {k}, ∀ {x : f k}, (k = 0) → P x)
  (h : ∀ {n k}, n = k + 1 →  (x : f (n) ) → (P x ∨ (∃ y : f k, R ⟨_ , y⟩ ⟨n , x⟩) ))
  {n : ℕ} (x : f n):
    ∃ k, ∃ (y : f k), P y ∧ R  ⟨_, y⟩ ⟨_, x⟩ := by
  set S := {k | ∃ (y : f k), R ⟨_, y⟩ ⟨_, x⟩}
  use (sInf S)
  obtain ⟨y, hy⟩ : (sInf S) ∈ S := by
    apply Nat.sInf_mem
    exact ⟨n, ⟨x, (hR' _)⟩⟩
  rcases (sInf S).eq_zero_or_eq_succ_pred with (hs | hs)
  exact ⟨y, ⟨h₀ hs, hy⟩⟩
  use y
  by_cases hy' : P y
  exact ⟨hy', hy⟩
  exfalso
  have := h hs y
  simp [hy'] at this
  obtain ⟨y', hy'⟩ := this
  have : (sInf S).pred ∈ S := ⟨y', hR hy' hy⟩
  apply (Nat.sInf_le this).not_lt (Nat.pred_lt _)
  rw [hs]
  apply Nat.succ_ne_zero

lemma forall_forall_iff_forall_and_of_eq (f : ℕ → Type*) (P : {n : ℕ} → f n → Prop)
  (R : (n : ℕ) × f n → (n : ℕ) × f n → Prop) :
    (∀ n : ℕ, ∀ x : f (n + 1), (P x ∨ (∃ y : f n, R ⟨_ , y⟩ ⟨_ , x⟩) ))
      ↔ ∀ {n k}, n = k + 1 →  ∀(x : f (n)), (P x ∨ (∃ y : f k, R ⟨_ , y⟩ ⟨n , x⟩)) := by
  constructor
  . intro h n k hnk x
    specialize h k
    rw [← hnk] at h
    exact h x
  . intro h n x
    apply h (by rfl)

end

namespace SSet

section Generator

universe u

variable (X : SSet.{u})

def connect := fun y : (n : ℕ) × X _[n] ↦ fun x : (n : ℕ) × X _[n] ↦
    ∃ φ, x.2 = X.map φ y.2

lemma connect.transitive :
    Transitive X.connect := by
  intro x y z ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩
  use φ₁ ≫ φ₂
  simp [h₁, h₂]

def connectBySurj := fun y : (n : ℕ) × X _[n] ↦ fun x : (n : ℕ) × X _[n] ↦
    ∃ φ : ([x.fst] : SimplexCategory) ⟶ [y.fst],
  (⇑φ.toOrderHom).Surjective ∧ x.2 = X.map φ.op y.2

variable {n : ℕ}
lemma exists_exsits_nondegenerate_and_connectBySurj (x : X _[n]) :
    ∃ k : ℕ, ∃ y : X _[k], Nondegenerate y ∧ connectBySurj X ⟨_, y⟩ ⟨_, x⟩ := by
  apply exists_and_of_transitive_of_reflexive
  . intro x y z ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩
    use φ₂ ≫ φ₁
    constructor
    . simp only [comp_toOrderHom, OrderHom.comp_coe]
      exact h₁.1.comp h₂.1
    . simp [h₂.2, h₁.2]
  . intro x
    use (𝟙 _)
    simp [Surjective]
  . intro _ _ h; apply Degenerate.eq_zero h
  . rw [← forall_forall_iff_forall_and_of_eq]
    intro n x
    simp only [Decidable.or_iff_not_imp_left, Nondegenerate, Degenerate.succ,
      mem_range, not_exists, not_forall, Decidable.not_not]
    rintro ⟨i, ⟨y, hy⟩⟩
    use y, (σ i)
    constructor
    . simp [σ]
      intro j
      by_cases hj : j ≤ i
      use j.castSucc
      rw [predAbove_castSucc_of_le _ _ hj]
      use j.succ
      rw [predAbove_succ_of_le _ _ (lt_of_not_le hj).le]
    . exact hy.symm

lemma standardSimplex.connect_iff_range_subset (x y: (k : ℕ) × Δ[n] _[k]) :
    Δ[n].connect x y ↔ range (asOrderHom y.2) ⊆ range (asOrderHom x.2) := by
  rw [← exists_OrderHom_comp_iff_range_subset]
  simp [connect, map_apply]
  constructor
  . intro ⟨φ, hφ⟩
    use (φ.unop).toOrderHom
    apply_fun fun x ↦ ⇑(asOrderHom x) at hφ
    exact hφ
  . intro ⟨h, h'⟩
    use op (Hom.mk h)
    ext : 2
    exact h'

lemma standardSimplex.range_subset_of_connect {n k k' : ℕ} (x : Δ[n] _[k])
  (y : Δ[n] _[k']) (φ):
    y = Δ[n].map φ x → range (asOrderHom y) ⊆ range (asOrderHom x) := by
  intro h
  exact (connect_iff_range_subset ⟨k, x⟩ ⟨k', y⟩).mp ⟨φ, h⟩

-- Generators of a SSet

structure Generator (X : SSet) where
  carrier : Set ((n : ℕ) × X _[n])
  connect : ∀ y, ∃ x ∈ carrier, X.connect x y

variable {X}

def isGenerator (S : Set ((n : ℕ) × X _[n])) : Prop :=
  ∀ y, ∃ x ∈ S, X.connect x y

def isGenerator.MkGenerator {X : SSet} (S : Set ((n : ℕ) × X _[n])) (h : isGenerator S):
  Generator X where
    carrier := S
    connect := h

lemma exists_nondegenerates_connect {X : SSet} {n : ℕ} (x : X _[n]) :
    ∃ k : ℕ, ∃ y : X _[k], Nondegenerate y ∧ X.connect ⟨_, y⟩ ⟨_, x⟩ := by
  apply exists_and_of_transitive_of_reflexive (hR := connect.transitive _)
  . intro x; use (𝟙 _); simp
  . intro _ _ h; apply Degenerate.eq_zero h
  . rw [← forall_forall_iff_forall_and_of_eq]
    intro n x
    simp [Decidable.or_iff_not_imp_left, Nondegenerates, Degenerate.succ]
    rintro i y hy
    exact ⟨y, ⟨(σ i).op, hy.symm⟩⟩

lemma Nondegenerates.isGenerator (X : SSet) :
    isGenerator X.Nondegenerates := by
  intro y
  simp only [Sigma.exists]
  apply exists_nondegenerates_connect

variable {Y : SSet} {n k : ℕ}

lemma hom_generator_ext {f g : X ⟶ Y} (G : X.Generator)
  (h : ∀ x ∈ G.carrier, f.app _ x.2 = g.app _ x.2) :
    f = g := by
  ext n x
  obtain ⟨y, ⟨hy₁, ⟨φ, hy₂⟩⟩⟩ := G.connect ⟨n.unop.len, x⟩
  have (h : X ⟶ Y) : h.app _ x = Y.map φ (h.app _ y.2) := by
    rw [← types_comp_apply (h.app (op [y.fst])) (Y.map φ), ← h.naturality,
        types_comp_apply, ← hy₂]; rfl
  rw [this, this, h _ (by apply hy₁)]

lemma connect_to_standardSimplex (x : Δ[n] _[k]) :
    Δ[n].connect ⟨n, objMk OrderHom.id⟩ ⟨k, x⟩ := by
  use op (Hom.mk (asOrderHom x))
  simp [map_apply]
  apply_fun objEquiv _ _
  ext; rfl

def standardSimplexGenerator : Generator Δ[n] where
  carrier := {⟨n, objMk OrderHom.id⟩}
  connect := by
    rintro ⟨k, y⟩
    use ⟨n, objMk OrderHom.id⟩
    simp only [mem_singleton_iff, true_and]
    apply connect_to_standardSimplex

def _root_.Set.level {X : (n : ℕ) → Type u} (S : Set ((n : ℕ) × X n)) (n : ℕ) :
    Set (X n) := {x | ⟨n, x⟩ ∈ S}

variable {Y : SSet.{u}}

def Compatible (S : Set ((n : ℕ) × X _[n])) (f : {n : ℕ} → S.level n → Y _[n]) :
    Prop :=
  ∀ x y : S, ∀ (z : (n : ℕ) × X _[n]), ∀ φ₁ φ₂, z.2 = X.map φ₁ x.1.2 → z.2 = X.map φ₂ y.1.2
    → Y.map φ₁ (f ⟨x.1.2, x.2⟩) = Y.map φ₂ (f ⟨y.1.2, y.2⟩)

def CompatibleOn (S : Set ((n : ℕ) × X _[n])) (f : {n : ℕ} → S.level n → Y _[n])
  (T : Set ((n : ℕ) × X _[n])) :
    Prop :=
  ∀ x y : S, ∀ z ∈ T, ∀ φ₁ φ₂, z.2 = X.map φ₁ x.1.2 → z.2 = X.map φ₂ y.1.2
    → Y.map φ₁ (f ⟨x.1.2, x.2⟩) = Y.map φ₂ (f ⟨y.1.2, y.2⟩)

structure CompatibleFun (S : Set ((n : ℕ) × X _[n])) (Y : SSet) where
  func : {n : ℕ} → S.level n → Y _[n]
  compatible : Compatible S func

noncomputable def Generator.extend
  (S : X.Generator) (f : CompatibleFun S.carrier Y) :
    X ⟶ Y where
  app m := by
    cases m with
    | op m =>
      induction m using SimplexCategory.rec
      intro x
      set y := choose <| S.connect ⟨_, x⟩
      have hy := choose_spec <| S.connect ⟨_, x⟩
      exact Y.map (choose hy.2) (f.1 ⟨y.2, hy.1⟩)
  naturality m₁ m₂ φ := by
    cases m₁ with
    | op m₁ =>
      cases m₂ with
      | op m₂ =>
        induction m₁ using SimplexCategory.rec
        induction m₂ using SimplexCategory.rec
        ext x
        dsimp only [SimplexCategory.rec, len_mk, types_comp_apply]
        set y := choose <| S.connect ⟨_, x⟩
        obtain ⟨hy, hy_⟩ := choose_spec <| S.connect ⟨_, x⟩
        set ψ := choose hy_
        have hψ := choose_spec hy_
        set y' := choose <| S.connect ⟨_, X.map φ x⟩
        obtain ⟨hy', hy'_⟩ := choose_spec <| S.connect ⟨_, X.map φ x⟩
        set ψ' := choose hy'_
        have hψ' := choose_spec hy'_
        simp at hψ hψ'
        have := f.2 ⟨y, hy⟩ ⟨y', hy'⟩ ⟨_, X.map φ x⟩ (ψ ≫ φ) ψ' (by simp; rw [hψ]) hψ'
        simp at this
        exact this.symm

lemma Generator.extend_spec (S : X.Generator) (f : CompatibleFun S.carrier Y) (x : X _[n])
  (hx : ⟨n, x⟩ ∈ S.carrier) :
    (S.extend f).app _ x = f.func ⟨x, hx⟩ := by
  simp [extend, SimplexCategory.rec]
  set y := choose <| S.connect ⟨_, x⟩
  obtain ⟨hy, hy_⟩ := choose_spec <| S.connect ⟨_, x⟩
  set ψ := choose hy_
  have hψ := choose_spec hy_
  convert f.2 ⟨y, hy⟩ ⟨⟨_, x⟩, hx⟩ ⟨_, x⟩ ψ (𝟙 _) hψ (by simp)
  simp only [FunctorToTypes.map_id_apply]

end Generator

section nface

variable {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 3))

def standardSimplex.nface :
    Δ[n + 2] _[n] :=
  objMk (j.succAboveOrderEmb.toOrderHom.comp i.succAboveOrderEmb.toOrderHom)

def standardSimplex.nface.hom : Δ[n] ⟶ Δ[n + 2] :=
  standardSimplex.map (δ i) ≫ standardSimplex.map (δ j)

lemma standardSimplex.nface.hom_eq_yonedaEquiv :
    nface.hom i j = (yonedaEquiv _ _).symm (nface i j) := rfl

def boundary.nface :
    ∂Δ[n + 2] _[n] :=
  ⟨standardSimplex.nface i j, by
    simp [standardSimplex.nface, OrderHom.comp]
    apply (not_imp_not.mpr Surjective.of_comp)
    simp [Surjective]⟩

def boundary.nface.hom : Δ[n] ⟶ ∂Δ[n + 2] := (yonedaEquiv _ _).symm (boundary.nface i j)

def horn.nface {k} (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Λ[n + 2, k] _[n] :=
  ⟨standardSimplex.nface i j, by
    simp [standardSimplex.nface, OrderHom.comp]
    by_contra h
    apply_fun Set.toFinset at h
    apply_fun Finset.card at h
    simp at h
    have := h ▸ Finset.card_insert_le _ _
    erw [Finset.card_image_of_injective _
        (Injective.comp j.succAboveOrderEmb.inj' i.succAboveOrderEmb.inj')] at this
    simp at this⟩

def horn.nface.hom {k} (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Δ[n] ⟶ Λ[n + 2, k] := (yonedaEquiv _ _).symm (horn.nface i j)

lemma standardSimplex.nface.range_asOrderHom_of_castSucc_lt (hij : i.castSucc < j):
    range (asOrderHom $ nface i j) = {i.castSucc, j}ᶜ :=
  range_succAbove_succAbove_of_castSucc_lt i j hij

end nface

section face

variable {n : ℕ} (i : Fin (n + 2))

def standardSimplex.face : Δ[n + 1] _[n] :=
    objMk i.succAboveOrderEmb.toOrderHom

def standardSimplex.face.hom : Δ[n] ⟶ Δ[n + 1] := standardSimplex.map (δ i)

lemma standardSimplex.face.hom_eq_yonedaEquiv :
    face.hom i = (yonedaEquiv _ _).symm (face i) := rfl

def boundary.face : ∂Δ[n + 1] _[n] :=
  ⟨standardSimplex.face i, by
    simp [asOrderHom_objMk, standardSimplex.face, OrderHom.comp, Surjective]⟩

def boundary.face.hom : Δ[n] ⟶ ∂Δ[n + 1] := (yonedaEquiv _ _).symm (boundary.face i)

lemma boundary.face.hom_comp_boundaryInclusion :
    face.hom i ≫ boundaryInclusion (n + 1) = standardSimplex.map (δ i) := rfl

def horn.face.hom (j : Fin (n + 2)) (h : j ≠ i) :
    Δ[n] ⟶ Λ[n + 1, i] := (yonedaEquiv _ _).symm (horn.face i j h)

lemma horn.face.hom_comp_boundaryInclusion {j : Fin (n + 2)} {h : j ≠ i} :
    face.hom i j h ≫ hornInclusion (n + 1) i = standardSimplex.map (δ j) := rfl

end face

section Degenerate

variable {n : ℕ}

lemma standardSimplex.face.nondegenerate (i : Fin (n + 2)) :
    Nondegenerate (X := Δ[n + 1]) (face i) :=
  (Nondegenerate.iff_StrictMono _).mpr i.succAboveOrderEmb.strictMono

lemma standardSimplex.face.exists_of_nondegenerate (x : Δ[n + 1] _[n]) :
    Nondegenerate x → ∃ i, x = face i := by
  rw [Nondegenerate.iff_StrictMono]
  intro h
  /-
  use toFace (OrderEmbedding.ofStrictMono _ h) 0
  ext : 2
  simp [face, asOrderHom_objMk]
  exact (toFace.function (OrderEmbedding.ofStrictMono _ h)).symm-/
  sorry

lemma standardSimplex.face.range_asOrderHom (i : Fin (n + 2)) :
    range (asOrderHom (face i)) = {i}ᶜ := range_succAbove i

lemma standardSimplex.nface.nondegenerate (i : Fin (n + 2)) (j : Fin (n + 3)) :
    Nondegenerate (nface i j) := by
  rw [Nondegenerate.iff_StrictMono]
  apply StrictMono.comp j.succAboveOrderEmb.strictMono i.succAboveOrderEmb.strictMono

end Degenerate

section Generator

def boundaryGenerator (n : ℕ) : Generator ∂Δ[n + 1] where
  carrier := {⟨n, boundary.face i⟩ | i : Fin (n + 2)}
  connect := by
    intro ⟨k, ⟨y, hy⟩⟩
    simp only [Surjective, len_mk, not_forall, not_exists] at hy
    obtain ⟨i, hi⟩ := hy
    simp only [len_mk, mem_setOf_eq, exists_exists_eq_and]
    use i
    simp only [connect, boundary, Subtype.mk.injEq]
    use op (factor_δ (objEquiv _ _ y) i)
    apply_fun objEquiv _ _
    convert (factor_δ_spec (objEquiv _ _ y) i hi).symm

def hornGenerator (n : ℕ) (j) : Generator Λ[n + 1, j] where
  carrier := {⟨n, horn.face j i.val i.property⟩| i : { i : Fin (n + 2) // i ≠ j}}
  connect := by
    intro ⟨k, ⟨y, hy⟩⟩
    rw [ne_univ_iff_exists_not_mem] at hy
    simp at hy
    obtain ⟨i, ⟨hi₁, hi₂⟩⟩ := hy
    simp only [len_mk, mem_setOf_eq, exists_exists_eq_and]
    use ⟨i, hi₁⟩
    simp only [connect, horn, Subtype.mk.injEq]
    use op (factor_δ (objEquiv _ _ y) i)
    apply_fun objEquiv _ _
    convert (factor_δ_spec (objEquiv _ _ y) i hi₂).symm

end Generator
#exit
section HomMk

/-
lemma test_aux2 (i j : Fin (n + 3)) (hij : i < j) :
  nface (i.castPred (ne_last_of_lt hij)) j
    = Δ[n + 2].map (δ (j.pred (ne_zero_of_lt hij))).op (face i) := by
  apply standardSimplex.ext
  simp [face, map_apply, nface, δ, asOrderHom_objMk]
  erw [asOrderHom_objMk]
  ext : 1
  simp [Hom.toOrderHom_mk (a := [n + 1]) (b := [n + 2]) (i.succAboveOrderEmb.toOrderHom),
        Hom.toOrderHom_mk (a := [n]) (b := [n + 1]) (j.pred _).succAboveOrderEmb.toOrderHom]
  ext k : 1
  simp [succAboveOrderEmb_apply, OrderEmbedding.toOrderHom, DFunLike.coe]
  by_cases hk : k.castSucc < i.castPred (ne_last_of_lt hij)
  . rw [succAbove_of_castSucc_lt _ _ hk, succAbove_of_castSucc_lt _ _
          (by rw [lt_iff_val_lt_val]; apply (lt_iff_val_lt_val.mp hk).trans hij)]
    rw [succAbove_of_castSucc_lt _ k
          (lt_of_lt_of_le hk (by rw [le_pred_iff]; simpa [le_iff_val_le_val, Nat.succ_le_iff])),
        succAbove_of_castSucc_lt _ _ (by rwa [lt_iff_val_lt_val] at hk ⊢)]
  . rw [not_lt] at hk
    by_cases hk' : k.succ.castSucc < j
    rw [succAbove_of_le_castSucc _ k hk, succAbove_of_castSucc_lt _ _ hk',
        succAbove_of_castSucc_lt _ k ((lt_pred_iff _).mpr hk'),
        succAbove_of_le_castSucc _ _ (by rwa [le_iff_val_le_val] at hk ⊢)]
    rfl
    . rw [not_lt] at hk'
      rw [succAbove_of_le_castSucc _ k hk, succAbove_of_le_castSucc _ _ hk',
          succAbove_of_le_castSucc _ k ((pred_le_iff _).mpr hk'),
          succAbove_of_le_castSucc _ _ (hij.le.trans hk')]
-/

lemma test_aux1 (x : Δ[n].obj k) (hx : Nondegenerate (n := k.unop.len) x) :
    ∀ k' (φ₁ : k ⟶ k') φ₂,
      (Δ[n].map φ₁ x = Δ[n].map φ₂ x → φ₁ = φ₂) := by
    intro k' φ₁ φ₂ h
    apply_fun unop using Quiver.Hom.unop_inj
    simp [map_apply] at h
    have : Mono ((objEquiv [n] k) x) := by
      rw [SimplexCategory.mono_iff_injective]
      exact ((Nondegenerate.iff_StrictMono _).mp hx).injective
    rwa [cancel_mono] at h

lemma test_aux3 (i j : Fin (n + 3)) (hij : i < j) (z : Δ[n + 2] _[k]) (φ₁) (φ₂) :
    z = Δ[n + 2].map φ₁ (face i) →
      z = Δ[n + 2].map φ₂ (face j) →
      ∃ φ, (φ₁ = (δ (j.pred (ne_zero_of_lt hij))).op ≫ φ) ∧
                 (φ₂ = (δ (i.castPred (ne_last_of_lt hij))).op ≫ φ) := by
  intro hi hj
  have aux1 :=
    (connect_iff_range_subset ⟨n + 1, face i⟩ ⟨_, z⟩).mp ⟨φ₁, hi⟩
  have aux2 :=
    (connect_iff_range_subset ⟨n + 1, face j⟩ ⟨_, z⟩).mp ⟨φ₂, hj⟩
  simp [asOrderHom_objMk] at aux1 aux2
  erw [Fin.range_succAbove] at aux1 aux2
  obtain ⟨φ, hφ⟩ : Δ[n + 2].connect ⟨_, (nface (i.castPred (ne_last_of_lt hij)) j)⟩ ⟨_ ,z⟩ := by
    rw [connect_iff_range_subset]
    simp [nface, asOrderHom_objMk]
    convert subset_inter aux1 aux2
    convert range_succAbove_succAbove_of_castSucc_lt (i.castPred (ne_last_of_lt hij)) j hij using 1
    rw [← compl_inj_iff, compl_compl, ← union_eq_compl_compl_inter_compl]
    rfl
  use φ
  constructor
  . apply test_aux1 _ (nondegenerate_face i)
    simp only [FunctorToTypes.map_comp_apply]
    erw [← hi, ← test_aux2 _ _ hij]
    exact hφ
  . apply test_aux1 _ (nondegenerate_face j)
    simp only [FunctorToTypes.map_comp_apply]
    erw [← hj]
    exact hφ
/-
variable {Y : SSet}

lemma test_aux4 (f : {k : ℕ} → (boundaryGenerator (n + 1)).carrier.level k → Y _[k]) :
    CompatibleOn _ f {⟨n, boundary.nface i j⟩ | (i : Fin (n + 2)) (j : Fin (n + 3))}
      → Compatible _ f := by
    intro h
    intro ⟨⟨n₁, x⟩, ⟨i, hi⟩⟩ ⟨⟨n₂, y⟩, ⟨j, hj⟩⟩ z φ₁ φ₂ hφ₁ hφ₂
    simp; simp at φ₁ φ₂
    cases hi; cases hj
    dsimp [boundary] at hφ₁ hφ₂
    by_cases hij : i = j
    . cases hij
      have : φ₁ = φ₂ := by
        apply test_aux1 _ (nondegenerate_face i)
        apply_fun Subtype.val at hφ₁ hφ₂
        exact hφ₁.symm.trans hφ₂
      rw [this]
    . rcases lt_or_gt_of_ne hij with hij | hij
      . obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₁) (congrArg Subtype.val hφ₂)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        exact h ⟨⟨_, boundary.face i⟩, by simp [boundaryGenerator]⟩
          ⟨⟨_, boundary.face j⟩, by simp [boundaryGenerator]⟩
          ⟨_, boundary.nface (i.castPred (ne_last_of_lt hij)) j⟩
          ⟨_, _, rfl⟩
          (δ (j.pred (ne_zero_of_lt hij))).op
          (δ (i.castPred (ne_last_of_lt hij))).op
          (by simp [boundary.nface, boundary.face, boundary]; apply test_aux2 _ _ hij)
          rfl
      . --- how to simplify this kind of symmetric proof??
        obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₂) (congrArg Subtype.val hφ₁)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        symm
        exact h ⟨⟨_, boundary.face j⟩, by simp [boundaryGenerator]⟩
          ⟨⟨_, boundary.face i⟩, by simp [boundaryGenerator]⟩
          ⟨_, boundary.nface (j.castPred (ne_last_of_lt hij)) i⟩
          ⟨_, _, rfl⟩
          (δ (i.pred (ne_zero_of_lt hij))).op
          (δ (j.castPred (ne_last_of_lt hij))).op
          (by simp [boundary.nface, boundary.face, boundary]; apply test_aux2 _ _ hij)
          rfl

-- extend the map on boundary along the faces

lemma boundary.face.injective : Injective (boundary.face (n := n)) := by
  intro i j hij
  apply_fun fun x ↦ ⇑(asOrderHom (Subtype.val x)) at hij
  simp only [face, face, asOrderHom_objMk] at hij
  apply succAbove_left_injective hij

-- this is interesting
noncomputable def equiv_test : Fin (n + 2) ≃ (boundaryGenerator n).carrier.level n where
  toFun i := ⟨boundary.face i, ⟨i, rfl⟩⟩
  invFun x := by
    have : ∃ i, boundary.face i = x.1 := by
      obtain ⟨i, hi⟩ := x.2
      exact ⟨i, heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi).2⟩
    exact (choose this)
  left_inv := by
    simp only [LeftInverse]
    intro i
    apply boundary.face.injective
    have := choose_spec
      (⟨boundary.face i, ⟨i, rfl⟩⟩ : (boundaryGenerator n).carrier.level n).property
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    rw [this]
  right_inv := by
    simp [Function.RightInverse, LeftInverse]
    intro x hx
    have : ∃ i, boundary.face i = x := by
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi).2⟩
    exact choose_spec this

noncomputable def CompatibleFun.boundaryMkFun {n : ℕ} (f : Fin (n + 2) → Y _[n]) :
    {k : ℕ} → (boundaryGenerator n).carrier.level k → Y _[k] := by
  intro k x
  have := x.2
  dsimp [boundaryGenerator, level] at this
  simp only [Sigma.mk.inj_iff, exists_and_left] at this
  cases this.1
  exact f (equiv_test.invFun x)

lemma CompatibleFun.boundaryMkFun_eq (f : Fin (n + 2) → Y _[n]) {h}:
    (CompatibleFun.boundaryMkFun f) ⟨boundary.face i, h⟩ = f i := by
  dsimp [boundaryMkFun]
  congr
  apply equiv_test.left_inv

lemma test_aux5 (k) (i : Fin (n + 2)) (j : Fin (n + 3)) (hij : i.castSucc < j) (φ):
    nface i j = Δ[n + 2].map φ (face k) → k = i.castSucc ∨ k = j := by
  intro h
  apply range_subset_of_connect at h
  rw [face.range_asOrderHom, nface.range_asOrderHom_of_castSucc_lt _ _ hij,
      compl_subset_compl] at h
  simp only [singleton_subset_iff, mem_insert_iff, mem_singleton_iff] at h
  exact h

lemma test_aux5'' (x : Δ[n + 2] _[n + 1]) (hx : Nondegenerate x) (i : Fin (n + 2)) (j : Fin (n + 3))
  (hij : i.castSucc < j) (φ):
    nface i j = Δ[n + 2].map φ x → x = face i.castSucc ∨ x = face j := by
  intro h
  obtain ⟨k, hk⟩ := exists_face_of_nondegenerate x hx
  cases hk
  apply test_aux5 _ _ _ hij at h
  cases h
  <;> rename Eq _ _ => h
  <;> simp [h]

lemma succAbove_succAbove_comm_of_castSucc_lt (i : Fin (n + 1)) (j : Fin (n + 2))
  (h : i.castSucc < j) :
    j.succAbove ∘ i.succAbove = i.castSucc.succAbove ∘ (j.pred (ne_zero_of_lt h)).succAbove :=
  sorry

lemma succAbove_succAbove_comm_of_lt_succ (i : Fin (n + 1)) (j : Fin (n + 2))
  (h : j < i.succ) :
    j.succAbove ∘ i.succAbove = i.succ.succAbove ∘ (j.castPred (ne_last_of_lt h)).succAbove :=
  sorry

-- corrolary of the next lemma
lemma test_aux5' (i : Fin (n + 2)) (j : Fin (n + 3))
  (hij : i.castSucc < j) (φ):
    nface i j = Δ[n + 2].map φ (face i.castSucc) → φ = (δ (j.pred (ne_zero_of_lt hij))).op := by
  intro h
  simp [map_apply, nface, face] at h
  apply Quiver.Hom.unop_inj
  ext : 2
  apply_fun fun f ↦ ⇑(Hom.toOrderHom f) at h
  simp at h
  simp [δ]
  erw [succAbove_succAbove_comm_of_castSucc_lt _ _ hij] at h
  apply Function.Injective.comp_left i.castSucc.succAboveOrderEmb.inj' h.symm

lemma test_aux5'rev (i : Fin (n + 2)) (j : Fin (n + 3)) (φ):
    nface i j = Δ[n + 2].map φ (face j) → φ = (δ i).op := by
  intro h
  simp [map_apply, nface, face] at h
  apply Quiver.Hom.unop_inj
  ext : 2
  apply_fun fun f ↦ ⇑(Hom.toOrderHom f) at h
  simp at h
  simp [δ]
  apply Function.Injective.comp_left j.succAboveOrderEmb.inj' h.symm

lemma test_aux6 (i : Fin (n + 2)) (j : Fin (n + 3)) :
  nface i j = nface (if h : i.castSucc < j then i else
    (j.castPred (ne_last_of_lt (lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))))
    (if i.castSucc < j then j else i.succ) := by
  split_ifs with h
  . rfl
  . simp [nface]
    ext : 2
    apply succAbove_succAbove_comm_of_lt_succ _ _
      ((lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))

lemma test_aux7 (i : Fin (n + 2)) (j : Fin (n + 3)) :
    (if h : i.castSucc < j then i else
      (j.castPred (ne_last_of_lt (lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _))))).castSucc
      < (if i.castSucc < j then j else i.succ) := by
  split_ifs with h
  . exact h
  . exact ((lt_of_le_of_lt (not_lt.mp h) (castSucc_lt_succ _)))

lemma test_aux8 [Preorder α] {a b c d : α} (h : a < b) (h' : c < d) :
    (a = c ∨ a = d) → (b = c ∨ b = d) → a = c ∧ b = d := by
  rintro (h₁ | h₁) (h₂ | h₂)
  . rw [h₁, h₂, lt_self_iff_false] at h; trivial
  . exact ⟨h₁, h₂⟩
  . rw [h₁, h₂] at h; apply False.elim ((lt_self_iff_false _).mp (h.trans h'))
  . rw [h₁, h₂, lt_self_iff_false] at h; trivial

-- for zero cases, we don't need `h`... how to intergrate the two cases?
noncomputable def CompatibleFun.boundaryMk {n : ℕ} (f : Fin (n + 3) → Y _[n + 1])
  (h : ∀ i j : Fin (n + 3), (hij : i < j) →
    Y.map (δ (j.pred (ne_zero_of_lt hij))).op (f i) =
      Y.map (δ (i.castPred (ne_last_of_lt hij))).op (f j)):
    CompatibleFun (boundaryGenerator (n + 1)).carrier Y where
  func := boundaryMkFun f
  compatible := by
    apply test_aux4
    intro ⟨x, ⟨xk, hxk⟩⟩ ⟨y, ⟨yk, hyk⟩⟩  z ⟨i, j, hij⟩ φ₁ φ₂ hφ₁ hφ₂
    cases hij; cases hxk; cases hyk
    simp at φ₁ φ₂; simp [boundary, boundary.nface, boundary.face] at hφ₁ hφ₂
    simp [CompatibleFun.boundaryMkFun_eq]
    by_cases hxy : xk = yk
    . cases hxy; congr!
      apply test_aux1 _ _ _ _ _ (hφ₁.symm.trans hφ₂)
      exact nondegenerate_face _
    . rw [test_aux6] at hφ₁ hφ₂
      rcases lt_or_gt_of_ne hxy with hxy | hxy
      . have := test_aux8 hxy (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₁)
          (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₂)
        rw [← this.2] at hφ₁ hφ₂
        rw [this.1] at hφ₁ hxy ⊢
        convert h _ _ hxy
        apply test_aux5' _ _ hxy _ hφ₁
        apply test_aux5'rev _ _ _ hφ₂
      . have := test_aux8 hxy (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₂)
          (test_aux5 _ _ _ (test_aux7 _ _) _ hφ₁)
        rw [← this.2] at hφ₁ hφ₂
        rw [this.1] at hxy hφ₂ ⊢
        symm
        convert h _ _ hxy
        apply test_aux5' _ _ hxy _ hφ₂
        apply test_aux5'rev _ _ _ hφ₁


noncomputable def boundary.HomMk  {n : ℕ} (f : Fin (n + 3) → Y _[n + 1])
  (h : ∀ i j : Fin (n + 3), (hij : i < j) →
    Y.map (δ (j.pred (ne_zero_of_lt hij))).op (f i) =
      Y.map (δ (i.castPred (ne_last_of_lt hij))).op (f j)) :
    ∂Δ[n + 2] ⟶ Y := Extend (boundaryGenerator (n + 1)) (CompatibleFun.boundaryMk f h)

noncomputable def CompatibleFun.boundaryMkZero (a b : Y _[0]) :
    CompatibleFun (boundaryGenerator 0).carrier Y where
  func := boundaryMkFun ![a, b]
  compatible := by
    intro ⟨x, ⟨xk, hxk⟩⟩ ⟨y, ⟨yk, hyk⟩⟩ z φ₁ φ₂ h₁ h₂
    cases hxk; cases hyk
    by_cases hxy : xk = yk
    . cases hxy; congr!
      simp at φ₁ φ₂
      apply Quiver.Hom.unop_inj
      ext; simp only [coe_fin_one]
    . apply_fun Subtype.val at h₁ h₂
      apply range_subset_of_connect at h₁
      apply range_subset_of_connect at h₂
      simp [boundary, boundary.face, face, asOrderHom_objMk] at h₁ h₂
      erw [range_succAbove] at h₁ h₂
      have : range ⇑(asOrderHom z.snd.val) = ∅ := by
        apply eq_empty_of_subset_empty
        convert subset_inter h₁ h₂
        rw [← compl_inj_iff, compl_empty, ← union_eq_compl_compl_inter_compl, eq_comm,
            ← toFinset_inj]
        apply Finset.eq_univ_of_card
        simp only [union_singleton, toFinset_insert, toFinset_singleton,
          Fintype.card_fin]
        rw [Finset.card_insert_of_not_mem (by simpa [Finset.mem_singleton, eq_comm]),
            Finset.card_singleton]
      simp only [range_eq_empty_iff, not_isEmpty_of_nonempty] at this

noncomputable def boundary.HomMkZero (a b : Y _[0]) :
    ∂Δ[1] ⟶ Y := Extend _ (CompatibleFun.boundaryMkZero a b)
-/

variable {Y : SSet.{u}}

lemma test2_aux1 (f : {k : ℕ} → (hornGenerator (n + 1) l).carrier.level k → Y _[k]) :
    CompatibleOn _ f {⟨n, horn.nface i j⟩ | (i : Fin (n + 2)) (j : Fin (n + 3))}
      → Compatible _ f := by
    intro h
    intro ⟨⟨n₁, x⟩, ⟨⟨i, hi₀⟩, hi⟩⟩ ⟨⟨n₂, y⟩, ⟨⟨j, hj₀⟩, hj⟩⟩ z φ₁ φ₂ hφ₁ hφ₂
    simp; simp at φ₁ φ₂
    cases hi; cases hj
    dsimp [horn] at hφ₁ hφ₂
    by_cases hij : i = j
    . cases hij
      have : φ₁ = φ₂ := by
        apply test_aux1 _ (face.nondegenerate i)
        apply_fun Subtype.val at hφ₁ hφ₂
        exact hφ₁.symm.trans hφ₂
      rw [this]
    . rcases lt_or_gt_of_ne hij with hij | hij
      . obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₁) (congrArg Subtype.val hφ₂)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        exact h ⟨⟨_, horn.face l i hi₀⟩, ⟨⟨i, hi₀⟩, rfl⟩⟩
          ⟨⟨_, horn.face l j hj₀⟩, ⟨⟨j, hj₀⟩, rfl⟩⟩
          ⟨_, horn.nface (i.castPred (ne_last_of_lt hij)) j⟩
          ⟨_, _, rfl⟩
          (δ (j.pred (ne_zero_of_lt hij))).op
          (δ (i.castPred (ne_last_of_lt hij))).op
          (by simp [horn.nface, horn.face, horn]; apply test_aux2 _ _ hij)
          rfl
      . --- how to simplify this kind of symmetric proof??
        obtain ⟨ψ, ⟨_, hψ₂⟩⟩ := test_aux3 _ _ hij _ _ _
          (congrArg Subtype.val hφ₂) (congrArg Subtype.val hφ₁)
        rw [hψ₂.1, hψ₂.2]
        simp only [FunctorToTypes.map_comp_apply]
        congr! 1
        symm
        exact h ⟨⟨_, horn.face l j hj₀⟩, ⟨⟨j, hj₀⟩, rfl⟩⟩
          ⟨⟨_, horn.face l i hi₀⟩, ⟨⟨i, hi₀⟩, rfl⟩⟩
          ⟨_, horn.nface (j.castPred (ne_last_of_lt hij)) i⟩
          ⟨_, _, rfl⟩
          (δ (i.pred (ne_zero_of_lt hij))).op
          (δ (j.castPred (ne_last_of_lt hij))).op
          (by simp [horn.nface, horn.face, horn]; apply test_aux2 _ _ hij)
          rfl

lemma horn.face.injective :
    ∀ j i i' : Fin (n + 2), ∀ h h', horn.face j i h =  horn.face j i' h' → i = i' := by
  intro _ _ _ _ _ hij
  apply_fun fun x ↦ ⇑(asOrderHom (Subtype.val x)) at hij
  simp only [face, face, asOrderHom_objMk] at hij
  apply succAbove_left_injective hij

noncomputable def equiv_test2 : Fin (n + 1) ≃ (hornGenerator n j).carrier.level n where
  toFun i := ⟨horn.face j _ (succAbove_ne j i), ⟨⟨_, succAbove_ne j i⟩, rfl⟩⟩
  invFun x := by
    have : ∃ i, horn.face j _ (succAbove_ne j i) = x.1 := by
      obtain ⟨⟨i', hi'₀⟩, hi'⟩ := x.2
      obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hi'₀
      use i
      convert (heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi').2)
    exact (choose this)
  left_inv := by
    simp only [LeftInverse]
    intro i
    apply succAbove_right_injective (p := j)
    apply horn.face.injective (j := j) _ _ (succAbove_ne j _) (succAbove_ne j _)
    exact choose_spec
      (⟨i, rfl⟩ : ∃ i', horn.face j _ (succAbove_ne j i') = horn.face j _ (succAbove_ne j i) )
  right_inv := by
    simp [Function.RightInverse, LeftInverse]
    intro x hx
    have : ∃ i, horn.face j _ (succAbove_ne j i) = x := by
      obtain ⟨⟨i', hi'₀⟩, hi'⟩ := hx
      obtain ⟨i, hi⟩ := exists_succAbove_eq_iff.mpr hi'₀
      use i
      convert (heq_eq_eq _ _ ▸ (Sigma.mk.inj_iff.mp hi').2)
    exact (choose_spec this)

noncomputable def CompatibleFun.hornMkFun {n : ℕ} (f : Fin (n + 1) → Y _[n]) (j):
    {k : ℕ} → (hornGenerator n j).carrier.level k → Y _[k] := by
  intro k x
  have := x.2
  dsimp [hornGenerator, level] at this
  simp only [Sigma.mk.inj_iff, exists_and_left] at this
  cases this.1
  exact f (equiv_test2.invFun x)

lemma CompatibleFun.hornMkFun_eq (f : Fin (n + 1) → Y _[n])
    (j : Fin (n + 2)) (i : Fin (n + 1)) {h} :
  (CompatibleFun.hornMkFun f j) ⟨horn.face j _ (succAbove_ne j i), h⟩ = f i := by
  dsimp [horn.face, hornMkFun]
  congr
  exact equiv_test2.left_inv i

noncomputable def CompatibleFun.hornMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    Y.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))).op (f i)
      = Y.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))).op (f j)) :
    CompatibleFun (hornGenerator (n + 1) k).carrier Y where
      func := CompatibleFun.hornMkFun f k
      compatible := by
        apply test2_aux1
        intro ⟨x, ⟨⟨xk, hxk₀⟩, hxk⟩⟩ ⟨y, ⟨⟨yk, hyk₀⟩, hyk⟩⟩ z ⟨i, j, hij⟩ φ₁ φ₂ h₁ h₂
        obtain ⟨xk, hxk₀⟩ := exists_succAbove_eq_iff.mpr hxk₀
        obtain ⟨yk, hyk₀⟩ := exists_succAbove_eq_iff.mpr hyk₀
        cases hxk₀; cases hyk₀; cases hxk; cases hyk; cases hij
        simp [horn.face, horn, ← Subtype.val_inj] at h₁ h₂
        simp at φ₁ φ₂
        simp [CompatibleFun.hornMkFun_eq]
        by_cases hxy : xk = yk
        . cases hxy; congr!
          apply test_aux1 _ _ _ _ _ (h₁.symm.trans h₂)
          exact nondegenerate_face _
        . simp [horn.nface] at h₁ h₂; rw [test_aux6] at h₁ h₂
          rcases lt_or_gt_of_ne hxy with hxy | hxy
          . have hxy' := strictMono_succAbove k hxy
            have := test_aux8 hxy' (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ h₁)
              (test_aux5 _ _ _ (test_aux7 _ _) _ h₂)
            rw [← this.2] at h₁ h₂
            rw [this.1] at hxy' h₁
            convert h _ _ hxy
            apply test_aux5' _ _ hxy' _ h₁
            simp [this.1]
            apply test_aux5'rev _ _ _ h₂
          . have hxy' := strictMono_succAbove k hxy
            have := test_aux8 hxy' (test_aux7 i j) (test_aux5 _ _ _ (test_aux7 _ _) _ h₂)
              (test_aux5 _ _ _ (test_aux7 _ _) _ h₁)
            rw [← this.2] at h₁ h₂
            rw [this.1] at hxy' h₂
            symm
            convert h _ _ hxy
            apply test_aux5' _ _ hxy' _ h₂
            simp [this.1]
            apply test_aux5'rev _ _ _ h₁

noncomputable def horn.HomMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    Y.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))).op (f i)
      = Y.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))).op (f j)) :
    Λ[n + 2, k] ⟶ Y := Extend (hornGenerator (n + 1) k) (CompatibleFun.hornMk f k h)

lemma horn.HomMk_spec {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3)) {l} {h} :
    (HomMk f k h).app _ (horn.face k _ (succAbove_ne k l)) = f l := by
  dsimp [HomMk]
  convert Extend.spec (hornGenerator (n + 1) k) (CompatibleFun.hornMk f k h)
    (horn.face k _ (succAbove_ne k l)) ⟨⟨_, succAbove_ne k l⟩, rfl⟩
  exact (CompatibleFun.hornMkFun_eq _ _ _).symm

lemma horn.face_comp_HomMk {n : ℕ} (f : Fin (n + 2) → Y _[n + 1]) (k : Fin (n + 3)) {l} {h} :
    (yonedaEquiv _ _).symm (horn.face k _ (succAbove_ne k l)) ≫ horn.HomMk f k h
      = (yonedaEquiv _ _).symm (f l) := by
  apply_fun Y.yonedaEquiv _
  convert HomMk_spec f k -- lhs is solved by rfl as they're definitionally equal
  simp only [Equiv.apply_symm_apply]

noncomputable def horn.HomMk' {n : ℕ} (f : Fin (n + 2) → (Δ[n + 1] ⟶ Y)) (k : Fin (n + 3))
  (h : ∀ i j : Fin (n + 2), (hij : i < j) →
    standardSimplex.map (δ ((k.succAbove j).pred
      (ne_zero_of_lt (strictMono_succAbove _ hij)))) ≫ (f i)
      = standardSimplex.map (δ ((k.succAbove i).castPred
        (ne_last_of_lt (strictMono_succAbove _ hij)))) ≫ (f j)) :
    Λ[n + 2, k] ⟶ Y := by
  apply Extend (hornGenerator (n + 1) k)
    (CompatibleFun.hornMk (fun i ↦ yonedaEquiv _ _ (f i)) k
      (by simpa only [yonedaEquiv_symm_naturality, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq]))

lemma horn.HomMk_spec' {n : ℕ} (f : Fin (n + 2) → (Δ[n + 1] ⟶ Y)) (k : Fin (n + 3)) {l} {h} :
    (yonedaEquiv _ _).symm (horn.face k _ (succAbove_ne k l)) ≫ HomMk' f k h = f l := by
  apply_fun yonedaEquiv _ _
  convert horn.HomMk_spec _ _

noncomputable def CompatibleFun.hornMkZero (a : Y _[0]) (k : Fin 2) :
    CompatibleFun (hornGenerator 0 k).carrier Y where
      func := hornMkFun ![a] k
      compatible := by
        intro ⟨x, ⟨⟨xk, hxk₀⟩, hxk⟩⟩ ⟨y, ⟨⟨yk, hyk₀⟩, hyk⟩⟩ z φ₁ φ₂ h₁ h₂
        have : ¬ xk = yk → 3 ≤ Fintype.card (Fin 2) := by
          intro h
          convert Finset.card_le_univ {k, xk, yk}
          rw [Finset.card_insert_of_not_mem (by simp only [Finset.mem_insert,
                  Finset.mem_singleton, not_or]; exact ⟨hxk₀.symm, hyk₀.symm⟩),
              Finset.card_insert_of_not_mem (by simp only [Finset.mem_singleton]; exact h),
              Finset.card_singleton]
        simp at this
        simp [horn.face, horn, ← Subtype.val_inj] at h₁ h₂
        cases hxk; cases hyk; cases this
        congr!
        apply test_aux1 _ _ _ _ _ (h₁.symm.trans h₂)
        exact nondegenerate_face _

noncomputable def horn.HomMkZero  (a : Y _[0]) (k : Fin 2) :
  Λ[1, k] ⟶ Y := Extend (hornGenerator 0 k) (CompatibleFun.hornMkZero a k)

end HomMk

end SSet
