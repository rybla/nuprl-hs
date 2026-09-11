-- | Landing page and per-example annotated documents.
module Pages
  ( indexPage
  , examplesIndexPage
  , examplePage
  , notFoundPage
  , countTheorems
  , countAbs
  , semanticKey
  , siteHeader
  , siteFooter
  ) where

import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

import Analyze
import Html
import Nuprl.Compute (normalize, whnf)
import Nuprl.Library
import Nuprl.Pretty (renderTerm)
import Nuprl.Proof (isComplete)
import Nuprl.Subst (alphaEq, freeVars)
import Nuprl.Term
import Render

--------------------------------------------------------------------------------
-- Shared chrome
--------------------------------------------------------------------------------

siteHeader :: Text -> Html
siteHeader root =
  el "a" [("class", "skip"), ("href", "#main")] (txt "Skip to content")
    </> el
      "header"
      [("class", "site")]
      ( el "a" [("class", "mark"), ("href", root <> "index.html")] (txt "nuprl-hs")
          <> el
            "nav"
            []
            ( navLink (root <> "index.html") "Home"
                <> navLink (root <> "examples.html") "Examples"
                <> navLink "https://github.com/rybla/nuprl-hs" "GitHub"
            )
      )
  where
    navLink href label = el "a" [("href", href)] (txt label)

siteFooter :: Html
siteFooter =
  el
    "footer"
    [("class", "site")]
    ( txt "nuprl-hs · "
        <> el "a" [("href", "https://github.com/rybla/nuprl-hs")] (txt "source")
    )

semanticKey :: Html
semanticKey =
  el "div" [("class", "key"), ("aria-label", "Semantic colour key")] $
    mconcat
      [ el "span" [("class", "sem-type")] (txt "types")
      , el "span" [("class", "sem-binder")] (txt "binders")
      , el "span" [("class", "sem-conn")] (txt "connectives")
      , el "span" [("class", "sem-tac")] (txt "tactics")
      , el "span" [("class", "sem-extract")] (txt "extracts")
      , el "span" [("class", "sem-goal")] (txt "goals")
      , el "span" [("class", "sem-abs")] (txt "abstractions")
      , el "span" [("class", "sem-comment")] (txt "comments")
      ]

--------------------------------------------------------------------------------
-- Landing page
--------------------------------------------------------------------------------

indexPage :: [AnnotatedExample] -> Html
indexPage exs =
  page
    ""
    "nuprl-hs — a modern implementation of NuPRL in Haskell"
    "A Haskell implementation of the NuPRL computational type theory proof development system, with annotated example theories."
    ( siteHeader ""
        </> el
          "main"
          [("id", "main")]
          ( el
              "div"
              [("class", "measure")]
              ( hero
                  </> links
                  </> examplesCallout exs
                  </> aboutSection
                  </> featuresSection
                  </> referencesSection
              )
          )
        </> siteFooter
    )

hero :: Html
hero =
  el "h1" [] (txt "nuprl-hs")
    </> el
      "p"
      [("class", "lede")]
      ( txt "A modern implementation of "
          <> el "em" [] (txt "NuPRL")
          <> txt ": computational type theory as a refinement theorem prover, with a tactic language, theory library, and a command-line interface."
      )

links :: Html
links =
  el "ul" [("class", "links")] $
    mconcat
      [ item "https://github.com/rybla/nuprl-hs" "github.com/rybla/nuprl-hs"
      , item "https://nuprl-web.cs.cornell.edu/" "Cornell PRL Project — Proof/Program Refinement Logic"
      ]
  where
    item href label = el "li" [] (el "a" [("href", href)] (txt label))

examplesCallout :: [AnnotatedExample] -> Html
examplesCallout exs =
  let n = length (orderExamples exs)
      nTh = sum (map countTheorems exs)
   in el "h2" [("id", "examples")] (txt "Annotated examples")
        </> el
          "p"
          []
          ( txt "Each theory in "
              <> el "code" [] (txt "examples/")
              <> txt " is checked by the kernel and rendered as an interactive document — statements and extracts first, then tactic scripts, refinement trees, and the analyses the CLI would print."
          )
        </> el
          "p"
          []
          ( el "a" [("href", "examples.html")] (txt "Browse the examples")
              <> txt (" · " <> T.pack (show n) <> " theories, " <> T.pack (show nTh) <> " theorems.")
          )

examplesIndexPage :: [AnnotatedExample] -> Html
examplesIndexPage exs =
  page
    ""
    "Examples — nuprl-hs"
    "Annotated example theories for nuprl-hs: interactive proofs, extracts, and kernel analyses."
    ( siteHeader ""
        </> el
          "main"
          [("id", "main")]
          ( el
              "div"
              [("class", "measure")]
              ( el "h1" [] (txt "Examples")
                  </> el
                    "p"
                    [("class", "lede")]
                    ( txt "Checked theories from "
                        <> el "code" [] (txt "examples/")
                        <> txt ", rendered as interactive documents. Statements and extracts are shown first; hover any connective, binder, or subterm for that piece of surface syntax and its uniform form; open a panel for the tactic script, the refinement tree, and the analyses the CLI would print ("
                        <> el "code" [] (txt "check")
                        <> txt ", "
                        <> el "code" [] (txt "extract")
                        <> txt ", "
                        <> el "code" [] (txt "compute")
                        <> txt ", "
                        <> el "code" [] (txt "dump")
                        <> txt ", "
                        <> el "code" [] (txt "show")
                        <> txt ")."
                    )
                  </> el "ol" [("class", "ex-index")] (mconcat (zipWith exampleEntry [1 ..] (orderExamples exs)))
              )
          )
        </> siteFooter
    )

exampleEntry :: Int -> AnnotatedExample -> Html
exampleEntry i ax =
  let meta = fromMaybe (fallbackMeta ax) (lookupMeta (axSlug ax))
      href = "examples/" <> axSlug ax <> ".html"
      nTh = countTheorems ax
      nAbs = countAbs ax
      n = if i < 10 then "0" <> T.pack (show i) else T.pack (show i)
   in el "li" [] $
        el "span" [("class", "n")] (txt n)
          <> el
            "div"
            []
            ( el "a" [("class", "title"), ("href", href)] (txt (emTitle meta))
                <> el "p" [("class", "tag")] (txt (emTagline meta))
                <> el
                  "p"
                  [("class", "meta")]
                  ( txt (T.pack (show nTh) <> " theorems")
                      <> txt " · "
                      <> txt (T.pack (show nAbs) <> " abstractions")
                      <> maybe emptyH (\c -> txt " · " <> el "span" [("class", "chap")] (txt c)) (emSection meta)
                  )
            )

fallbackMeta :: AnnotatedExample -> ExampleMeta
fallbackMeta ax =
  ExampleMeta
    { emSlug = axSlug ax
    , emTitle = theoryName (axTheory ax)
    , emTagline = "A checked .nuprl theory."
    , emSection = Nothing
    }

orderExamples :: [AnnotatedExample] -> [AnnotatedExample]
orderExamples exs =
  let want = map emSlug exampleMetas
      findSlug s = case filter (\e -> axSlug e == s) exs of
        e : _ -> Just e
        [] -> Nothing
      ordered = mapMaybe findSlug want
      rest = filter (\e -> axSlug e `notElem` want) exs
   in ordered ++ rest

aboutSection :: Html
aboutSection =
  el "h2" [("id", "about")] (txt "nuprl and nuprl-hs")
    </> el
      "p"
      []
      ( txt "The " <> el "a" [("href", "https://nuprl-web.cs.cornell.edu/html/NuprlSystem.html")] (txt "original NuPRL system") <> txt " is an X11 structured editor driven from an ML top loop. This port keeps the "
          <> el "em" [] (txt "logic")
          <> txt " — sequents, primitive refinement rules, extracts, soft encodings, universe levels — and replaces the window system with a file-based proof language and a command-line interface."
      )
    </> el
      "p"
      []
      ( txt "Computational type theory is a constructive foundation in the lineage of Martin-Löf: a proposition is a type, a proof is a program, and completing a refinement proof "
          <> el "em" [] (txt "extracts")
          <> txt " that program. The kernel is a pure function from sequents to subgoals and extract combinators. Tactics search for kernel derivations; they are not part of the trusted computing base."
      )

featuresSection :: Html
featuresSection =
  el "h2" [("id", "features")] (txt "Notable features")
    </> el
      "dl"
      [("class", "feats")]
      ( feat "Refinement sequents"
          "Goals are H ⊢ C, with hidden hypotheses and %-invisible variables, matching NuPRL §9.12."
          <> feat "Primitive rules"
          "hyp, intro, elim, eq, compute, cut, lemma, thin, decide — the whole of a completed proof is a tree of these."
          <> feat "LCF tactics"
          "THEN, THENL, ORELSE, REPEAT, TRY, auto, arith, and the usual intro/elim/hyp family."
          <> feat "Soft logic encodings"
          "True = Unit, False = Void, ∧ = ×, ∨ = ⊎, ⇒ = →, ∀ = Π, ∃ = Σ, t ∈ A = t = t ∈ A."
          <> feat "Program extraction"
          "The extract of a complete proof is recovered from each node's combinator. Identity extracts to λA. λx. x."
          <> feat "Lazy computation"
          "Weak-head reduction with β, arithmetic, spread, decide, list_ind, integer ind, and soft unfold."
          <> feat "File-based theories"
          "theory / abs / theorem / proof / qed. The checker replays scripts."
      )
  where
    feat n d = el "dt" [] (txt n) <> el "dd" [] (txt d)

referencesSection :: Html
referencesSection =
  el "h2" [("id", "references")] (txt "References")
    </> el
      "ol"
      []
      ( ref "Implementing Mathematics with the Nuprl Proof Development System, R. L. Constable et al., Prentice-Hall, 1986."
          "https://nuprl-web.cs.cornell.edu/book/"
          <> ref "P. B. Jackson, The Nuprl Proof Development System, Version 4.2: Reference Manual and User’s Guide, Cornell University, 1995."
          "https://nuprl-web.cs.cornell.edu/html/NuprlSystem.html"
          <> ref "P. Martin-Löf, Intuitionistic Type Theory, Bibliopolis, 1984."
          "https://nuprl-web.cs.cornell.edu/"
          <> ref "Cornell PRL project — Proof/Program Refinement Logic."
          "https://nuprl-web.cs.cornell.edu/"
          <> ref "github.com/rybla/nuprl-hs"
          "https://github.com/rybla/nuprl-hs"
      )
    </> el
      "p"
      [("class", "note")]
      ( txt "Colour on this site is semantic: Prussian blue for types, verdigris with a dotted underline for binders, oxblood for connectives, forest for tactics and kernel rules, burnt sienna for extracts, ochre for sequent goals, slate indigo for named abstractions. The same key is used on every page."
      )
  where
    ref title href =
      el "li" [] (el "a" [("href", href)] (txt title))

--------------------------------------------------------------------------------
-- Example pages
--------------------------------------------------------------------------------

examplePage :: AnnotatedExample -> Html
examplePage ax =
  let meta = fromMaybe (fallbackMeta ax) (lookupMeta (axSlug ax))
      title = emTitle meta <> " — nuprl-hs"
      desc = emTagline meta
   in page
        "../"
        title
        desc
        ( siteHeader "../"
            </> el
              "main"
              [("id", "main")]
              ( el
                  "div"
                  [("class", "ex-layout")]
                  ( toc ax
                      <> el
                        "div"
                        []
                        ( exampleHero ax meta
                            <> semanticKey
                            <> toolbar
                            <> maybe emptyH (\e -> el "p" [("class", "error")] (txt e)) (axError ax)
                            <> mconcat (map (renderItem (axLibrary ax)) (axItems ax))
                            <> sourcePanel ax
                        )
                  )
              )
            </> siteFooter
        )

exampleHero :: AnnotatedExample -> ExampleMeta -> Html
exampleHero ax meta =
  el "p" [("class", "kind")] (txt ("theory " <> theoryName (axTheory ax)))
    </> el "h1" [] (txt (emTitle meta))
    </> el "p" [("class", "lede")] (txt (emTagline meta))
    </> maybe emptyH (\c -> el "p" [("class", "note")] (txt c)) (emSection meta)
    </> ( if T.null (axHeader ax)
            then emptyH
            else el "div" [("class", "guide")] (mconcat (map para (splitParas (axHeader ax))))
        )
    </> el
      "p"
      [("class", "note")]
      ( txt (T.pack (show (countTheorems ax)))
          <> txt " theorems, "
          <> txt (T.pack (show (countAbs ax)))
          <> txt " abstractions, checked by replaying their tactic scripts on the kernel. Hover any piece of syntax for its kind, surface form, and uniform term; open Tactics, Proof, or Analysis to go deeper."
      )
  where
    para t = el "p" [] (txt t)

splitParas :: Text -> [Text]
splitParas = filter (not . T.null) . map T.strip . T.splitOn "\n\n"

toolbar :: Html
toolbar =
  el "div" [("class", "toolbar")] $
    el "button" [("type", "button"), ("id", "expand-all")] (txt "Open all panels")
      <> voidEl "input" [("id", "filter"), ("type", "search"), ("placeholder", "Filter by name"), ("aria-label", "Filter objects by name")]

toc :: AnnotatedExample -> Html
toc ax =
  el "nav" [("class", "toc"), ("aria-label", "On this page")] $
    el "h2" [] (txt "Contents")
      <> el
        "ol"
        []
        ( mconcat (map tocItem (axItems ax))
            <> el "li" [] (el "a" [("href", "#source")] (txt "Source"))
        )
  where
    tocItem = \case
      ItemTheorem th ->
        el "li" [] (el "a" [("href", "#" <> athName th)] (txt (athName th)))
      ItemAbs a ->
        el "li" [] (el "a" [("class", "abs-link"), ("href", "#" <> opIdText (absOpId a))] (txt (opIdText (absOpId a))))
      _ -> emptyH

renderItem :: Library -> AnnotatedItem -> Html
renderItem lib = \case
  ItemComment _ t ->
    el "div" [("class", "card")] (el "p" [("class", "prose")] (txt t))
  ItemSoft ns ->
    el "div" [("class", "card")] $
      el "div" [("class", "kind abs")] (txt "soft")
        <> el
          "p"
          [("class", "soft-line")]
          ( txt "Soft abstractions, transparent to tactics: "
              <> el "span" [("class", "sem-abs")] (txt (T.intercalate ", " ns))
              <> txt "."
          )
  ItemAbs a -> absCard lib a
  ItemTheorem th -> theoremCard lib th

absCard :: Library -> Abstraction -> Html
absCard lib a =
  let name = opIdText (absOpId a)
      formals = absFormals a
      sig =
        txt name
          <> ( if null formals
                 then emptyH
                 else
                   raw "("
                     <> mconcat (punctuate (raw " ; ") (map formalH formals))
                     <> raw ")"
             )
   in el "article" [("class", "card"), ("id", name), ("data-name", name)] $
        el "div" [("class", "kind abs")] (txt (if absSoft a then "soft abstraction" else "abstraction"))
          <> el "h3" [("class", "obj-name")] sig
          <> el
            "div"
            [("class", "statement")]
            ( tok
                KConn
                "≡"
                "Definitional equality of an abstraction: the right-hand side is the unfolding used by the kernel."
                <> raw " "
                <> renderTermH lib (absRhs a)
            )
          <> el
            "details"
            [("class", "panel")]
            ( el "summary" [] (txt "Analysis")
                <> el
                  "dl"
                  [("class", "analysis")]
                  ( row "uniform" (uniformTerm (absRhs a))
                      <> row "weak-head" (renderTerm (whnf (absRhs a)))
                      <> ( if termSize (absRhs a) <= 80
                             then row "normal form" (renderTerm (normalize (absRhs a)))
                             else emptyH
                         )
                      <> row "soft" (if absSoft a then "yes — tactics treat this as transparent" else "no")
                  )
            )
  where
    formalH bt =
      let vs = btVars bt
          body = btBody bt
       in ( if null vs
              then renderTermH lib body
              else mconcat (punctuate (raw ", ") (map binder vs)) <> raw ". " <> renderTermH lib body
          )
    punctuate _ [] = []
    punctuate _ [x] = [x]
    punctuate s (x : xs) = x : s : punctuate s xs
    row k v = el "dt" [] (txt k) <> el "dd" [] (txt (shorten 400 v))

theoremCard :: Library -> AnnotatedTheorem -> Html
theoremCard lib th =
  let name = athName th
      st = athStats th
      complete = maybe False isComplete (athProof th) && athError th == Nothing
      status =
        el
          "span"
          [("class", if complete then "status" else "status bad")]
          ( txt
              ( if complete
                  then "complete · " <> T.pack (show (psNodes st)) <> " rules"
                  else maybe "incomplete" id (athError th)
              )
          )
   in el "article" [("class", "card"), ("id", name), ("data-name", name)] $
        el "div" [("class", "card-head")] (el "div" [("class", "kind theorem")] (txt "theorem") <> status)
          <> el "h3" [("class", "obj-name")] (txt name)
          <> el "div" [("class", "statement")] (renderTermH lib (athGoal th))
          <> maybe emptyH (extractBlock lib) (athExtract th)
          <> el
            "details"
            [("class", "panel")]
            ( el "summary" [] (txt "Tactics")
                <> renderScriptH lib (athScript th)
            )
          <> maybe
            emptyH
            ( \p ->
                el
                  "details"
                  [("class", "panel proof-panel")]
                  ( el "summary" [] (txt "Proof")
                      <> renderProofH lib p
                  )
            )
            (athProof th)
          <> el
            "details"
            [("class", "panel")]
            ( el "summary" [] (txt "Analysis")
                <> theoremAnalysis lib th
            )

extractBlock :: Library -> Term -> Html
extractBlock lib e =
  el "div" [("class", "extract-line")] $
    el "span" [("class", "k")] (txt "extract")
      <> raw " "
      <> renderTermH lib e

theoremAnalysis :: Library -> AnnotatedTheorem -> Html
theoremAnalysis lib th =
  let g = athGoal th
      st = athStats th
      w = whnf g
      uni = uniformTerm g
      fvs = Set.toList (freeVars g)
      rules =
        T.intercalate
          ", "
          [ n <> " × " <> T.pack (show k)
          | (n, k) <- psRules st
          ]
   in el "dl" [("class", "analysis")] $
        row "status" (if athError th == Nothing then "complete" else maybe "failed" id (athError th))
          <> row "refinement steps" (T.pack (show (psNodes st)))
          <> row "open goals" (T.pack (show (psOpen st)))
          <> (if null (psRules st) then emptyH else row "kernel rules" rules)
          <> ( if null (psLemmas st)
                 then emptyH
                 else row "lemmas" (T.intercalate ", " (psLemmas st))
             )
          <> row "goal (uniform)" uni
          <> (if alphaEq w g then emptyH else row "goal, weak-head" (renderTerm w))
          <> row
            "free variables"
            ( if null fvs
                then "none (closed)"
                else T.intercalate ", " (map varText fvs)
            )
          <> maybe emptyH (extractFacts lib) (athExtract th)
  where
    row k v = el "dt" [] (txt k) <> el "dd" [] (txt (shorten 500 v))

extractFacts :: Library -> Term -> Html
extractFacts _lib e =
  let w = whnf e
      n = if termSize e <= 80 then Just (normalize e) else Nothing
      row k v = el "dt" [] (txt k) <> el "dd" [] (txt (shorten 500 v))
   in row "extract (uniform)" (uniformTerm e)
        <> (if alphaEq w e then emptyH else row "extract, weak-head" (renderTerm w))
        <> maybe
          emptyH
          ( \nf ->
              if alphaEq nf e || alphaEq nf w then emptyH else row "extract, normal form" (renderTerm nf)
          )
          n
        <> row
          "extract sort"
          ( if isCanonicalValue e
              then "canonical value"
              else "neutral / non-canonical"
          )

sourcePanel :: AnnotatedExample -> Html
sourcePanel ax =
  el "article" [("class", "card"), ("id", "source")] $
    el "div" [("class", "kind")] (txt "source")
      <> el "h3" [("class", "obj-name")] (txt ("examples/" <> axSlug ax <> ".nuprl"))
      <> el
        "details"
        [("class", "panel")]
        ( el "summary" [] (txt "Original source file")
            <> renderSourceH (axSource ax)
        )

notFoundPage :: Html
notFoundPage =
  page
    ""
    "Not found — nuprl-hs"
    "That page is not part of the nuprl-hs site."
    ( siteHeader ""
        </> el
          "main"
          [("id", "main")]
          ( el
              "div"
              [("class", "measure")]
              ( el "h1" [] (txt "Not found")
                  <> el "p" [] (txt "This path is not part of the static site.")
                  <> el "p" [] (el "a" [("href", "index.html")] (txt "Return to the landing page."))
              )
          )
        </> siteFooter
    )

countTheorems :: AnnotatedExample -> Int
countTheorems ax = length [() | ItemTheorem _ <- axItems ax]

countAbs :: AnnotatedExample -> Int
countAbs ax = length [() | ItemAbs _ <- axItems ax]