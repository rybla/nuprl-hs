-- | Tiny HTML combinators for the static site. No templating library: every
-- page is a self-contained document with relative links (GitHub Pages).
module Html
  ( Html
  , fromHtml
  , txt
  , raw
  , emptyH
  , el
  , el_
  , voidEl
  , page
  , (</>)
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy (toStrict)
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as B

-- | An HTML fragment.
newtype Html = Html Builder
  deriving newtype (Semigroup, Monoid)

fromHtml :: Html -> Text
fromHtml (Html b) = toStrict (B.toLazyText b)

-- | Escaped text node.
txt :: Text -> Html
txt = Html . B.fromText . escapeText

-- | Unescaped markup. Only for trusted fragments assembled by this builder.
raw :: Text -> Html
raw = Html . B.fromText

emptyH :: Html
emptyH = mempty

-- | Concatenate with a newline (readable source HTML).
(</>) :: Html -> Html -> Html
a </> b = a <> raw "\n" <> b
infixr 5 </>

el :: Text -> [(Text, Text)] -> Html -> Html
el name attrs body =
  raw "<"
    <> raw name
    <> foldMap attr attrs
    <> raw ">"
    <> body
    <> raw "</"
    <> raw name
    <> raw ">"

el_ :: Text -> [(Text, Text)] -> Html
el_ name attrs = el name attrs emptyH

voidEl :: Text -> [(Text, Text)] -> Html
voidEl name attrs =
  raw "<" <> raw name <> foldMap attr attrs <> raw ">"

attr :: (Text, Text) -> Html
attr (k, v) = raw " " <> raw k <> raw "=\"" <> raw (escapeAttr v) <> raw "\""

escapeText :: Text -> Text
escapeText =
  T.replace "&" "&amp;"
    . T.replace "<" "&lt;"
    . T.replace ">" "&gt;"

escapeAttr :: Text -> Text
escapeAttr =
  T.replace "\"" "&quot;"
    . T.replace "'" "&#39;"
    . T.replace "\n" " "
    . T.replace "\r" ""
    . escapeText

-- | Full HTML5 document. @root@ is the relative path from this file to the
-- site root (@""@ on the landing page, @"../"@ on example pages).
page :: Text -> Text -> Text -> Html -> Html
page root title description body =
  raw "<!DOCTYPE html>"
    </> el
      "html"
      [("lang", "en")]
      ( el
          "head"
          []
          ( voidEl "meta" [("charset", "utf-8")]
              </> voidEl
                "meta"
                [ ("name", "viewport")
                , ("content", "width=device-width, initial-scale=1")
                ]
              </> el "title" [] (txt title)
              </> voidEl "meta" [("name", "description"), ("content", description)]
              </> voidEl
                "link"
                [ ("rel", "icon")
                , ("href", root <> "favicon.svg")
                , ("type", "image/svg+xml")
                ]
              </> voidEl
                "link"
                [ ("rel", "stylesheet")
                , ("href", root <> "css/site.css")
                ]
          )
          </> el
            "body"
            []
            ( body
                </> el_ "div" [("id", "tip"), ("role", "tooltip"), ("hidden", "hidden")]
                </> el "script" [("src", root <> "js/site.js")] emptyH
            )
      )
