use ::serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::cell::Cell;
use std::ops::Deref;

use crate::arc::ArcX;
use crate::base::RcBase;
use crate::rc::RcX;
use crate::refcount::RefCount;

impl<T, C> Serialize for RcBase<T, C>
where
    T: ?Sized + Serialize,
    C: RefCount,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        Ok(self.deref().serialize(serializer)?)
    }
}

impl<T, C> Serialize for RcX<T, C>
where
    T: ?Sized + Serialize,
    Cell<C>: RefCount,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        Ok(self.0.serialize(serializer)?)
    }
}

impl<T, C> Serialize for ArcX<T, C>
where
    T: ?Sized + Serialize,
    C: RefCount + Send + Sync,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        Ok(self.0.serialize(serializer)?)
    }
}

impl<'de, T, C> Deserialize<'de> for RcBase<T, C>
where
    T: ?Sized,
    Box<T>: Deserialize<'de>,
    C: RefCount,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let b = Box::<T>::deserialize(deserializer)?;
        Ok(RcBase::from(b))
    }
}

impl<'de, T, C> Deserialize<'de> for RcX<T, C>
where
    T: ?Sized,
    Box<T>: Deserialize<'de>,
    Cell<C>: RefCount,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(RcX(RcBase::deserialize(deserializer)?))
    }
}

impl<'de, T, C> Deserialize<'de> for ArcX<T, C>
where
    T: ?Sized,
    Box<T>: Deserialize<'de>,
    C: RefCount + Send + Sync,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(ArcX(RcBase::deserialize(deserializer)?))
    }
}

#[cfg(test)]
mod tests {
    use ::serde::{Deserialize, Serialize};
    use serde_json::Result;

    use crate::{Arc8, Rc8};

    #[derive(Serialize, Deserialize)]
    struct SizedData {
        value: String,
    }

    #[test]
    fn rc_ser_sized() -> Result<()> {
        let orig = Rc8::new(SizedData {
            value: String::from("compact-rc"),
        });

        assert_eq!(orig.value, "compact-rc");

        let json = serde_json::to_string(&orig)?;
        let de: Box<SizedData> = serde_json::from_str(&json)?;

        assert_eq!(de.value, orig.value);

        Ok(())
    }

    #[test]
    fn arc_ser_sized() -> Result<()> {
        let orig = Arc8::new(SizedData {
            value: String::from("compact-rc"),
        });

        assert_eq!(orig.value, "compact-rc");

        let json = serde_json::to_string(&orig)?;
        let de: Box<SizedData> = serde_json::from_str(&json)?;

        assert_eq!(de.value, orig.value);

        Ok(())
    }

    #[test]
    fn rc_ser_str() -> Result<()> {
        let orig: Rc8<str> = Rc8::from("compact-rc");

        assert_eq!(&*orig, "compact-rc");

        let json = serde_json::to_string(&orig)?;
        let de: Box<str> = serde_json::from_str(&json)?;

        assert_eq!(&*de, &*orig);

        Ok(())
    }

    #[test]
    fn arc_ser_str() -> Result<()> {
        let orig: Arc8<str> = Arc8::from("compact-rc");

        assert_eq!(&*orig, "compact-rc");

        let json = serde_json::to_string(&orig)?;
        let de: Box<str> = serde_json::from_str(&json)?;

        assert_eq!(&*de, &*orig);

        Ok(())
    }

    #[test]
    fn rc_de_sized() -> Result<()> {
        const JSON: &str = r#"
        {
            "value": "compact-rc"
        }
        "#;

        let rc: Rc8<SizedData> = serde_json::from_str(JSON)?;

        assert_eq!(rc.value, "compact-rc");

        Ok(())
    }

    #[test]
    fn arc_de_sized() -> Result<()> {
        const JSON: &str = r#"
        {
            "value": "compact-rc"
        }
        "#;

        let rc: Arc8<SizedData> = serde_json::from_str(JSON)?;

        assert_eq!(rc.value, "compact-rc");

        Ok(())
    }

    #[test]
    fn rc_de_str() -> Result<()> {
        const JSON: &str = "\"compact-rc\"";

        let de: Rc8<str> = serde_json::from_str(JSON)?;

        assert_eq!(&*de, "compact-rc");

        Ok(())
    }

    #[test]
    fn arc_de_str() -> Result<()> {
        const JSON: &str = "\"compact-rc\"";

        let de: Arc8<str> = serde_json::from_str(JSON)?;

        assert_eq!(&*de, "compact-rc");

        Ok(())
    }
}
